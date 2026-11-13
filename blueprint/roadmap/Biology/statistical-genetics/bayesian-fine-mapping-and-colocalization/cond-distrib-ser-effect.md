# The effect posterior of the single-effect regression

**The effect posterior of the single-effect regression** (Wang et al. 2020): given
`y = x β + e` with `β ~ N(0, σ₀²)` independent of `e ~ N(0, σ² I)`, for almost every `y` the
effect is normal with mean `σ₀² / (σ₀² + s²) · β̂` and variance `σ₀² s² / (σ₀² + s²)`, where
`β̂ = olsEffect x y` and `s² = olsVar σ2 x`.
