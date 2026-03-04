;; Kinetic Quadratic DAO Governance Contract

;; Implements dynamic quadratic voting with reputation-weighted participation,
;; dual-token architecture (governance + kinetic tokens), and momentum-based
;; voting power that adapts based on community engagement and stake duration.

;; ============================================================
;; CONSTANTS
;; ============================================================

(define-constant CONTRACT-OWNER tx-sender)
(define-constant ERR-NOT-AUTHORIZED (err u100))
(define-constant ERR-PROPOSAL-NOT-FOUND (err u101))
(define-constant ERR-PROPOSAL-EXPIRED (err u102))
(define-constant ERR-PROPOSAL-ACTIVE (err u103))
(define-constant ERR-ALREADY-VOTED (err u104))
(define-constant ERR-INSUFFICIENT-TOKENS (err u105))
(define-constant ERR-INVALID-AMOUNT (err u106))
(define-constant ERR-TRANSFER-FAILED (err u107))
(define-constant ERR-INVALID-PROPOSAL-STATE (err u108))
(define-constant ERR-MEMBER-NOT-FOUND (err u109))
(define-constant ERR-STAKE-LOCKED (err u110))

;; Governance parameters
(define-constant PROPOSAL-DURATION u1440)          ;; ~10 days in blocks
(define-constant MIN-PROPOSAL-THRESHOLD u1000)     ;; min governance tokens to propose
(define-constant QUORUM-THRESHOLD u500000)         ;; total voting power needed for quorum
(define-constant APPROVAL-THRESHOLD u60)           ;; 60% approval required
(define-constant MAX-VOTES-PER-PROPOSAL u100)      ;; quadratic cost ceiling per proposal
(define-constant KINETIC-EARN-RATE u10)            ;; kinetic tokens earned per governance action
(define-constant MAX-REPUTATION u1000)             ;; reputation cap per domain
(define-constant STAKE-LOCK-BLOCKS u144)           ;; ~1 day minimum stake lock

;; ============================================================
;; DATA VARS
;; ============================================================

(define-data-var proposal-count uint u0)
(define-data-var total-governance-supply uint u0)
(define-data-var total-kinetic-supply uint u0)
(define-data-var treasury-balance uint u0)
(define-data-var contract-active bool true)

;; ============================================================
;; DATA MAPS
;; ============================================================

;; Governance token balances
(define-map governance-balances
  principal
  uint)

;; Kinetic token balances (participation momentum)
(define-map kinetic-balances
  principal
  uint)

;; Staked governance tokens
(define-map staked-governance
  principal
  { amount: uint, staked-at: uint, unlock-at: uint })

;; Member reputation per domain
;; Domains: u0=general, u1=technical, u2=financial, u3=governance, u4=community
(define-map member-reputation
  { member: principal, domain: uint }
  uint)

;; Member activity metadata
(define-map member-metadata
  principal
  { joined-at: uint, total-votes: uint, proposals-created: uint, last-active: uint })

;; Proposals
(define-map proposals
  uint
  { creator: principal,
    title: (string-ascii 128),
    description: (string-ascii 512),
    domain: uint,
    created-at: uint,
    expires-at: uint,
    status: uint,          ;; 0=active, 1=passed, 2=rejected, 3=cancelled
    yes-power: uint,
    no-power: uint,
    total-voters: uint,
    treasury-request: uint,
    executed: bool })

;; Vote records per proposal per voter
(define-map vote-records
  { proposal-id: uint, voter: principal }
  { vote-count: uint,   ;; raw number of votes cast
    direction: bool,    ;; true=yes, false=no
    voting-power: uint, ;; actual quadratic power used
    cast-at: uint })

;; Prediction market stakes on proposal outcomes
(define-map prediction-stakes
  { proposal-id: uint, predictor: principal }
  { predicted-outcome: bool, staked-kinetic: uint })

;; ============================================================
;; PRIVATE HELPERS
;; ============================================================

;; Integer square root via Newton's method (Clarity-safe iteration)
(define-private (isqrt (n uint))
  (if (is-eq n u0)
    u0
    (let ((x0 (+ u1 (/ n u2))))
      (let ((x1 (/ (+ x0 (/ n x0)) u2)))
        (let ((x2 (/ (+ x1 (/ n x1)) u2)))
          (let ((x3 (/ (+ x2 (/ n x2)) u2)))
            (let ((x4 (/ (+ x3 (/ n x3)) u2)))
              (if (<= x4 x3) x4 x3))))))))

;; Compute quadratic cost: cost = votes^2 governance tokens burned
(define-private (quadratic-cost (votes uint))
  (* votes votes))

;; Get effective reputation weight for a member in a domain (1-10 scale)
(define-private (get-reputation-weight (member principal) (domain uint))
  (let ((rep (default-to u0 (map-get? member-reputation { member: member, domain: domain }))))
    (+ u1 (/ rep u100))))  ;; base 1, +1 per 100 rep points, max ~11

;; Get stake duration bonus multiplier (longer stake = more power)
(define-private (get-stake-multiplier (member principal))
  (match (map-get? staked-governance member)
    stake-data
      (let ((duration (- block-height (get staked-at stake-data))))
        (if (>= duration u10080)  ;; ~70 days
          u3
          (if (>= duration u2880)  ;; ~20 days
            u2
            u1)))
    u1))

;; Compute total voting power for a member on a domain proposal
;; Power = isqrt(votes) * reputation-weight * stake-multiplier
(define-private (compute-voting-power (member principal) (votes uint) (domain uint))
  (let ((base-power (isqrt votes))
        (rep-weight (get-reputation-weight member domain))
        (stake-mult (get-stake-multiplier member)))
    (* base-power (* rep-weight stake-mult))))

;; Accrue kinetic tokens to a member for participation
(define-private (accrue-kinetic (member principal) (amount uint))
  (let ((current (default-to u0 (map-get? kinetic-balances member))))
    (map-set kinetic-balances member (+ current amount))
    (var-set total-kinetic-supply (+ (var-get total-kinetic-supply) amount))))

;; Increment reputation for a member in a domain, capped at MAX-REPUTATION
(define-private (increment-reputation (member principal) (domain uint) (amount uint))
  (let ((current (default-to u0 (map-get? member-reputation { member: member, domain: domain })))
        (new-rep (+ current amount)))
    (map-set member-reputation
      { member: member, domain: domain }
      (if (> new-rep MAX-REPUTATION) MAX-REPUTATION new-rep))))

;; Update member last-active block
(define-private (touch-member (member principal))
  (match (map-get? member-metadata member)
    data (map-set member-metadata member (merge data { last-active: block-height }))
    true))

;; ============================================================
;; TOKEN MANAGEMENT
;; ============================================================

;; Mint governance tokens (owner only) -- used for initial distribution
(define-public (mint-governance (recipient principal) (amount uint))
  (begin
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (asserts! (> amount u0) ERR-INVALID-AMOUNT)
    (let ((current (default-to u0 (map-get? governance-balances recipient))))
      (map-set governance-balances recipient (+ current amount))
      (var-set total-governance-supply (+ (var-get total-governance-supply) amount))
      ;; Register member if new
      (if (is-none (map-get? member-metadata recipient))
        (map-set member-metadata recipient
          { joined-at: block-height, total-votes: u0,
            proposals-created: u0, last-active: block-height })
        true)
      (ok amount))))

;; Transfer governance tokens between principals
(define-public (transfer-governance (amount uint) (recipient principal))
  (let ((sender-balance (default-to u0 (map-get? governance-balances tx-sender))))
    (asserts! (> amount u0) ERR-INVALID-AMOUNT)
    (asserts! (>= sender-balance amount) ERR-INSUFFICIENT-TOKENS)
    (map-set governance-balances tx-sender (- sender-balance amount))
    (map-set governance-balances recipient
      (+ (default-to u0 (map-get? governance-balances recipient)) amount))
    (ok amount)))

;; Stake governance tokens to boost voting power
(define-public (stake-governance (amount uint))
  (let ((balance (default-to u0 (map-get? governance-balances tx-sender))))
    (asserts! (> amount u0) ERR-INVALID-AMOUNT)
    (asserts! (>= balance amount) ERR-INSUFFICIENT-TOKENS)
    ;; Deduct from liquid balance
    (map-set governance-balances tx-sender (- balance amount))
    ;; Add to stake (accumulate if already staked)
    (let ((existing (default-to { amount: u0, staked-at: block-height, unlock-at: u0 }
                      (map-get? staked-governance tx-sender))))
      (map-set staked-governance tx-sender
        { amount: (+ (get amount existing) amount),
          staked-at: block-height,
          unlock-at: (+ block-height STAKE-LOCK-BLOCKS) }))
    ;; Reward kinetic tokens for staking commitment
    (accruekinetic-on-stake tx-sender amount)
    (ok amount)))

;; Internal helper to reward kinetic on stake
(define-private (accruekinetic-on-stake (member principal) (amount uint))
  (accrue-kinetic member (/ amount u100)))

;; Unstake governance tokens after lock period
(define-public (unstake-governance)
  (match (map-get? staked-governance tx-sender)
    stake-data
      (begin
        (asserts! (>= block-height (get unlock-at stake-data)) ERR-STAKE-LOCKED)
        (let ((amount (get amount stake-data)))
          (map-delete staked-governance tx-sender)
          (map-set governance-balances tx-sender
            (+ (default-to u0 (map-get? governance-balances tx-sender)) amount))
          (ok amount)))
    ERR-MEMBER-NOT-FOUND))

;; ============================================================
;; PROPOSALS
;; ============================================================

;; Create a new governance proposal
(define-public (create-proposal
  (title (string-ascii 128))
  (description (string-ascii 512))
  (domain uint)
  (treasury-request uint))
  (let ((sender-balance (default-to u0 (map-get? governance-balances tx-sender)))
        (proposal-id (+ (var-get proposal-count) u1)))
    (asserts! (var-get contract-active) ERR-NOT-AUTHORIZED)
    (asserts! (>= sender-balance MIN-PROPOSAL-THRESHOLD) ERR-INSUFFICIENT-TOKENS)
    (asserts! (<= domain u4) ERR-INVALID-AMOUNT)  ;; valid domain 0-4
    ;; Store proposal
    (map-set proposals proposal-id
      { creator: tx-sender,
        title: title,
        description: description,
        domain: domain,
        created-at: block-height,
        expires-at: (+ block-height PROPOSAL-DURATION),
        status: u0,
        yes-power: u0,
        no-power: u0,
        total-voters: u0,
        treasury-request: treasury-request,
        executed: false })
    (var-set proposal-count proposal-id)
    ;; Update member metadata
    (match (map-get? member-metadata tx-sender)
      data (map-set member-metadata tx-sender
              (merge data { proposals-created: (+ (get proposals-created data) u1),
                            last-active: block-height }))
      true)
    ;; Reward kinetic and reputation for proposing
    (accrue-kinetic tx-sender KINETIC-EARN-RATE)
    (increment-reputation tx-sender domain u5)
    (ok proposal-id)))

;; Cast a quadratic vote on a proposal
;; votes: raw number of votes (cost = votes^2 governance tokens burned)
;; direction: true = yes, false = no
(define-public (cast-vote (proposal-id uint) (votes uint) (direction bool))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND))
        (cost (quadratic-cost votes))
        (sender-balance (default-to u0 (map-get? governance-balances tx-sender))))
    ;; Validations
    (asserts! (is-eq (get status proposal) u0) ERR-INVALID-PROPOSAL-STATE)
    (asserts! (< block-height (get expires-at proposal)) ERR-PROPOSAL-EXPIRED)
    (asserts! (is-none (map-get? vote-records { proposal-id: proposal-id, voter: tx-sender }))
              ERR-ALREADY-VOTED)
    (asserts! (> votes u0) ERR-INVALID-AMOUNT)
    (asserts! (<= votes MAX-VOTES-PER-PROPOSAL) ERR-INVALID-AMOUNT)
    (asserts! (>= sender-balance cost) ERR-INSUFFICIENT-TOKENS)
    ;; Burn quadratic cost from balance
    (map-set governance-balances tx-sender (- sender-balance cost))
    (var-set total-governance-supply (- (var-get total-governance-supply) cost))
    ;; Compute adaptive voting power
    (let ((power (compute-voting-power tx-sender votes (get domain proposal))))
      ;; Record vote
      (map-set vote-records { proposal-id: proposal-id, voter: tx-sender }
        { vote-count: votes, direction: direction,
          voting-power: power, cast-at: block-height })
      ;; Update proposal tallies
      (map-set proposals proposal-id
        (merge proposal
          { yes-power: (if direction (+ (get yes-power proposal) power) (get yes-power proposal)),
            no-power:  (if direction (get no-power proposal) (+ (get no-power proposal) power)),
            total-voters: (+ (get total-voters proposal) u1) }))
      ;; Update member metadata
      (match (map-get? member-metadata tx-sender)
        data (map-set member-metadata tx-sender
                (merge data { total-votes: (+ (get total-votes data) u1),
                              last-active: block-height }))
        true)
      ;; Reward kinetic and reputation for voting
      (accrue-kinetic tx-sender (+ KINETIC-EARN-RATE votes))
      (increment-reputation tx-sender (get domain proposal) u2)
      (ok power))))

;; Finalize a proposal after expiry -- anyone can call
(define-public (finalize-proposal (proposal-id uint))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
    (asserts! (is-eq (get status proposal) u0) ERR-INVALID-PROPOSAL-STATE)
    (asserts! (>= block-height (get expires-at proposal)) ERR-PROPOSAL-ACTIVE)
    (let ((total-power (+ (get yes-power proposal) (get no-power proposal)))
          (yes-power   (get yes-power proposal)))
      (let ((quorum-met (>= total-power QUORUM-THRESHOLD))
            (yes-pct    (if (> total-power u0) (/ (* yes-power u100) total-power) u0)))
        (let ((new-status
                (if (and quorum-met (>= yes-pct APPROVAL-THRESHOLD))
                  u1   ;; passed
                  u2)));; rejected
          (map-set proposals proposal-id (merge proposal { status: new-status }))
          ;; Reward creator reputation on pass
          (if (is-eq new-status u1)
            (increment-reputation (get creator proposal) (get domain proposal) u10)
            true)
          (ok new-status))))))

;; Execute a passed proposal's treasury request (owner/multisig in production)
(define-public (execute-proposal (proposal-id uint) (recipient principal))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (asserts! (is-eq (get status proposal) u1) ERR-INVALID-PROPOSAL-STATE)
    (asserts! (not (get executed proposal)) ERR-INVALID-PROPOSAL-STATE)
    (let ((request (get treasury-request proposal)))
      (asserts! (<= request (var-get treasury-balance)) ERR-INSUFFICIENT-TOKENS)
      (var-set treasury-balance (- (var-get treasury-balance) request))
      (map-set proposals proposal-id (merge proposal { executed: true }))
      (ok request))))

;; Cancel an active proposal (creator or owner only)
(define-public (cancel-proposal (proposal-id uint))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND)))
    (asserts! (is-eq (get status proposal) u0) ERR-INVALID-PROPOSAL-STATE)
    (asserts! (or (is-eq tx-sender (get creator proposal))
                  (is-eq tx-sender CONTRACT-OWNER)) ERR-NOT-AUTHORIZED)
    (map-set proposals proposal-id (merge proposal { status: u3 }))
    (ok true)))

;; ============================================================
;; PREDICTION MARKET
;; ============================================================

;; Stake kinetic tokens predicting a proposal outcome
(define-public (predict-outcome (proposal-id uint) (predicted-outcome bool) (kinetic-amount uint))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND))
        (kbalance  (default-to u0 (map-get? kinetic-balances tx-sender))))
    (asserts! (is-eq (get status proposal) u0) ERR-INVALID-PROPOSAL-STATE)
    (asserts! (< block-height (get expires-at proposal)) ERR-PROPOSAL-EXPIRED)
    (asserts! (is-none (map-get? prediction-stakes { proposal-id: proposal-id, predictor: tx-sender }))
              ERR-ALREADY-VOTED)
    (asserts! (>= kbalance kinetic-amount) ERR-INSUFFICIENT-TOKENS)
    (map-set kinetic-balances tx-sender (- kbalance kinetic-amount))
    (map-set prediction-stakes { proposal-id: proposal-id, predictor: tx-sender }
      { predicted-outcome: predicted-outcome, staked-kinetic: kinetic-amount })
    (ok kinetic-amount)))

;; Claim prediction reward after proposal finalized
(define-public (claim-prediction-reward (proposal-id uint))
  (let ((proposal (unwrap! (map-get? proposals proposal-id) ERR-PROPOSAL-NOT-FOUND))
        (stake     (unwrap! (map-get? prediction-stakes { proposal-id: proposal-id, predictor: tx-sender })
                            ERR-MEMBER-NOT-FOUND)))
    (asserts! (not (is-eq (get status proposal) u0)) ERR-PROPOSAL-ACTIVE)
    (let ((outcome-passed (is-eq (get status proposal) u1)))
      (if (is-eq (get predicted-outcome stake) outcome-passed)
        (let ((reward (* (get staked-kinetic stake) u2)))  ;; 2x reward for correct prediction
          (accrue-kinetic tx-sender reward)
          (increment-reputation tx-sender (get domain proposal) u3)
          (ok reward))
        (ok u0)))))  ;; No reward on wrong prediction (kinetic already burned on stake)

;; ============================================================
;; TREASURY
;; ============================================================

;; Deposit STX into treasury
(define-public (deposit-treasury (amount uint))
  (begin
    (asserts! (is-eq tx-sender CONTRACT-OWNER) ERR-NOT-AUTHORIZED)
    (asserts! (> amount u0) ERR-INVALID-AMOUNT)
    (var-set treasury-balance (+ (var-get treasury-balance) amount))
    (ok (var-get treasury-balance))))

;; ============================================================
;; READ-ONLY FUNCTIONS
;; ============================================================

(define-read-only (get-proposal (proposal-id uint))
  (map-get? proposals proposal-id))

(define-read-only (get-vote (proposal-id uint) (voter principal))
  (map-get? vote-records { proposal-id: proposal-id, voter: voter }))

(define-read-only (get-governance-balance (member principal))
  (default-to u0 (map-get? governance-balances member)))

(define-read-only (get-kinetic-balance (member principal))
  (default-to u0 (map-get? kinetic-balances member)))

(define-read-only (get-stake-info (member principal))
  (map-get? staked-governance member))

(define-read-only (get-reputation (member principal) (domain uint))
  (default-to u0 (map-get? member-reputation { member: member, domain: domain })))

(define-read-only (get-member-metadata (member principal))
  (map-get? member-metadata member))

(define-read-only (get-prediction (proposal-id uint) (predictor principal))
  (map-get? prediction-stakes { proposal-id: proposal-id, predictor: predictor }))

(define-read-only (get-protocol-stats)
  { total-proposals: (var-get proposal-count),
    total-governance-supply: (var-get total-governance-supply),
    total-kinetic-supply: (var-get total-kinetic-supply),
    treasury-balance: (var-get treasury-balance) })

(define-read-only (get-voting-power-preview (member principal) (votes uint) (domain uint))
  (compute-voting-power member votes domain))

(define-read-only (get-quadratic-cost (votes uint))
  (quadratic-cost votes))
