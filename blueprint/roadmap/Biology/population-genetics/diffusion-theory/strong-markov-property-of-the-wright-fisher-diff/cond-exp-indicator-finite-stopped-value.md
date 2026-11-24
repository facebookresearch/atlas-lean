# Strong Markov property for multi-time functionals

Let `μ` be a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a real
process with continuous paths, adapted to `(ℱ_t)`. Write `π(y) = min(max(y, 0), 1)` for the clamp of
a real number to `[0, 1]`, through which the states of `X` are read. Suppose that `X` is Markov with
respect to `(ℱ_t)` with the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
`T`: for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,
`μ[g(π X_t) | ℱ_s] = (T_{t - s} g)(π X_s)` `μ`-almost everywhere. Let `τ` be an `(ℱ_t)`-stopping
time with values in `[0, ∞]` and `ℱ_τ` its σ-algebra. Then for all times `t_1 ≤ ⋯ ≤ t_n` and every
bounded measurable `F : [0, 1]^n → ℝ`,

`μ[1_{τ < ∞} F(π X_{τ + t_1}, …, π X_{τ + t_n}) | ℱ_τ] = 1_{τ < ∞} ∫ F dQ_{0, t}(π X_τ, ·)`
`μ`-almost everywhere,

where `Q_{0, t}` is the
[finite-dimensional kernel](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/finite-chain-kernel.md)
of the
[neutral Wright–Fisher kernels](../construction-of-the-neutral-wright-fisher-diffus/neutral-kernel.md)
at the times `t = (t_1, …, t_n)`, the law at these times of the neutral Wright–Fisher diffusion.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
