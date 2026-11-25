# Strong Markov property for whole-path functionals

Let `μ` be a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a real
process with continuous paths, adapted to `(ℱ_t)`. Write `π(y) = min(max(y, 0), 1)` for the clamp of
a real number to `[0, 1]`, through which the states of `X` are read. Suppose that `X` is Markov with
respect to `(ℱ_t)` with the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
`T`: for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,
`μ[g(π X_t) | ℱ_s] = (T_{t - s} g)(π X_s)` `μ`-almost everywhere. Let `τ` be an `(ℱ_t)`-stopping
time with values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Then for every bounded measurable `F` on the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md) `[0, ∞) → [0, 1]`
(product σ-algebra),

`μ[1_{τ < ∞} F((π X_{τ + u})_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F dP_{π X_τ}` `μ`-almost everywhere,

where `P_y` is the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) of the
neutral Wright–Fisher diffusion started at `y`: on `{τ < ∞}`, the conditional law given `ℱ_τ` of the
clamped future path `(π X_{τ + u})_{u ≥ 0}` is `P_{π X_τ}`. Nothing is asserted about the unclamped
path `(X_{τ + u})_{u ≥ 0}`, which need not take values in `[0, 1]`.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
