# Neutral Wright–Fisher diffusion semigroup

The neutral Wright–Fisher diffusion semigroup on `C([0, 1], ℝ)`, time in units of `M = 2N`
generations: `wfSemigroup t f` is the uniform limit of `(wfStep M)^⌊tM⌋ f` as `M → ∞`
(`tendsto_wfStep_pow_floor`). For `t < 0` it is the identity (a junk value: `⌊tM⌋₊ = 0`).
