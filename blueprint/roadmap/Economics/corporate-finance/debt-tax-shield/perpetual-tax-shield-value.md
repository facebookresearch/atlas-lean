# Perpetual riskless-debt tax shield

Under the discounting assumptions of
`taxShieldValue` (perpetual debt, constant riskless rate `rD > 0`, constant tax rate,
interest deducted every period), the shield value is `τ * D`. The proof is a
specialization of `growingPerpetuity_eq` at growth `g = 0`: the shield
sum equals `growingPerpetuity (τ * rD * D) rD 0`, and the Gordon-growth formula
gives `τ * rD * D / rD = τ * D`.
