# Equiv

Raw likelihood equality: `likelihood (M.toHMM θ) y n = likelihood (M.toHMM θ') y n` for every
`n` and every observation sequence `y`. When `M` is regular (`M.Regular`) and `θ, θ' ∈ M.Θ`, this
expresses equality of the stationary observation laws of `θ` and `θ'`.
