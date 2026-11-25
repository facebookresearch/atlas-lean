# Strong Markov property with selection for bounded test functions

Let `κ = (κ_t)_{t ≥ 0}` be a [Feller](is-feller-family.md) family of Markov kernels on `[0, 1]`, `μ`
a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration, `σ` a real number and `X`
a [Wright–Fisher diffusion with selection `σ`, Markov for `κ`](is-selection-markov.md), with respect
to `(ℱ_t)` and `μ`: `X` is a continuous `(ℱ_t)`-adapted solution with values in `[0, 1]` of the
[martingale problem](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with selection `σ`, and `μ[g(X_t) | ℱ_s] = ∫ g(y) κ_{t - s}(X_s, dy)` `μ`-almost everywhere for all
times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`. Let `τ` be an `(ℱ_t)`-stopping time with
values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Then for every time `t ≥ 0` and every bounded measurable
`g : [0, 1] → ℝ`,

`μ[1_{τ < ∞} g(X_{τ + t}) | ℱ_τ] = 1_{τ < ∞} ∫ g(y) κ_t(X_τ, dy)` `μ`-almost everywhere.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
