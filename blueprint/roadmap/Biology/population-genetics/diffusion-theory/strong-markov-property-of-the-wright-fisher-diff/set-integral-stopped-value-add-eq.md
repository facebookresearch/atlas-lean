# Strong Markov property, integrated form

Let `μ` be a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a real
process with continuous paths, adapted to `(ℱ_t)`. Write `π(y) = min(max(y, 0), 1)` for the clamp of
a real number to `[0, 1]`, through which the states of `X` are read. Suppose that `X` is Markov with
respect to `(ℱ_t)` with the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
`T`: for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,
`μ[g(π X_t) | ℱ_s] = (T_{t - s} g)(π X_s)` `μ`-almost everywhere. Let `τ` be an `(ℱ_t)`-stopping
time with values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Then for every `A ∈ ℱ_τ`, every time `t ≥ 0`
and every continuous `g : [0, 1] → ℝ`,

`∫_{A ∩ {τ < ∞}} g(π X_{τ + t}) dμ = ∫_{A ∩ {τ < ∞}} (T_t g)(π X_τ) dμ`.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
