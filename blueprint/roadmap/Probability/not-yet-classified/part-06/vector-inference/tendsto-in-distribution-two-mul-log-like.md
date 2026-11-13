# Wilks' theorem, vector parameter, simple null

Under the hypotheses of
`tendstoInDistribution_waldStatistic`, if moreover the log-density `θ ↦ log p θ x` is
differentiable on the ball (so the score is its true gradient there) and `(θ, x) ↦ p θ x` is
jointly measurable, then the likelihood-ratio statistic
`2 (ℓₙ(θhat n) - ℓₙ(θ₀))`, `ℓₙ θ = ∑_{i<n} log p θ (X i)`, evaluated at the consistent root
`θhat n` (not the supremum `sup_θ ℓₙ θ`), converges in distribution to `χ²_d`, `d = dim E ≥ 1`.
Composite nulls with `r` restrictions (limit `χ²_r`) are not covered.

The proof expands `ℓₙ` to second order around `θ₀` (`abs_log_sub_sub_sub_le`) and shows
`2 (ℓₙ(θhat n) - ℓₙ(θ₀)) - n ⟪I(θ₀) (θhat n - θ₀), θhat n - θ₀⟫ → 0` in probability.

## Sources

- Wilks (1938); van der Vaart (1998), Theorem 16.7.
