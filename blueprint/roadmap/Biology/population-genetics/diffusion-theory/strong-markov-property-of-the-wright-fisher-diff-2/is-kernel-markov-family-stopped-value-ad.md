# The process after a stopping time is a Markov family

Let `κ = (κ_t)_{t ≥ 0}` be a [Feller](is-feller-family.md) family of kernels on `[0, 1]`, `μ` a
finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a real process with
continuous paths, adapted to `(ℱ_t)`. Write `π(y) = min(max(y, 0), 1)` for the clamp of a real
number to `[0, 1]`, through which the states of `X` are read. Suppose that `X` is Markov for `κ`:
for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,
`μ[g(π X_t) | ℱ_s] = ∫ g(y) κ_{t - s}(π X_s, dy)` `μ`-almost everywhere. Let `τ` be an
`(ℱ_t)`-stopping time with values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Then the process
`u ↦ π X_{τ + u}` is a [Markov family for `κ`](is-kernel-markov-family.md) with respect to the
[filtration after `τ`](../strong-markov-property-of-the-wright-fisher-diff/post-filtration.md)
`(ℱ_{τ + u})_{u ≥ 0}`, under `μ` restricted to `{τ < ∞}`.
