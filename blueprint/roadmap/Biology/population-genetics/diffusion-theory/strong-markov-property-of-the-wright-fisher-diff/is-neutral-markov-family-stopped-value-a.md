# The process after a stopping time is a Markov family

Let `μ` be a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a real
process with continuous paths, adapted to `(ℱ_t)`. Write `π(y) = min(max(y, 0), 1)` for the clamp of
a real number to `[0, 1]`, through which the states of `X` are read. Suppose that `X` is Markov with
respect to `(ℱ_t)` with the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
`T`: for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,
`μ[g(π X_t) | ℱ_s] = (T_{t - s} g)(π X_s)` `μ`-almost everywhere. Let `τ` be an `(ℱ_t)`-stopping
time with values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Let `Y_u` be the clamped stopped value of `X`
at `τ + u`: `Y_u = π X_{τ + u}` on `{τ < ∞}`, and on `{τ = ∞}` the value of `π X` at the default
finite time that the stopped-value convention assigns, so that `Y_u` is defined on all of `Ω`. Then
`(Y_u)_{u ≥ 0}` is a [Markov family](is-neutral-markov-family.md) for the neutral Wright–Fisher
semigroup with respect to the [filtration after `τ`](post-filtration.md) `(ℱ_{τ + u})_{u ≥ 0}` under
`μ` restricted to `{τ < ∞}`: each `Y_u` is `ℱ_{τ + u}`-measurable on `Ω`, and the integral identity
holds for the restricted measure.
