# Greenwood's variance estimate

**Greenwood's variance estimate** of the Kaplan–Meier estimate at `t`:
`V̂(t) = Ŝ(t)² ∑_{tⱼ ≤ t, dⱼ < Yⱼ} dⱼ / (Yⱼ (Yⱼ - dⱼ))`.

This is Greenwood's plug-in *estimate* of the variance of `Ŝ(t)`, not the exact sampling variance
of the Kaplan–Meier estimator. Domain convention: the textbook summand is undefined when
`dⱼ = Yⱼ` (the Kaplan–Meier factor is `0`), so such times are explicitly excluded from the sum
rather than divided by zero. If no such time occurs by `t` the definition is the textbook formula
(`greenwoodVariance_eq_textbook`), and if
one occurs with `dⱼ > 0` at or before `t` then `Ŝ(t) = 0` and `V̂(t) = 0`
(`greenwoodVariance_eq_zero_of_deaths_eq_atRisk`).
