# Strong Markov property with selection for multi-time functionals

Let `κ = (κ_t)_{t ≥ 0}` be a [Feller](is-feller-family.md) family of Markov kernels on `[0, 1]`, `μ`
a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration, `σ` a real number and `X`
a [Wright–Fisher diffusion with selection `σ`, Markov for `κ`](is-selection-markov.md), with respect
to `(ℱ_t)` and `μ`; its values lie in `[0, 1]`. Let `τ` be an `(ℱ_t)`-stopping time with values in
`[0, ∞]` and `ℱ_τ` its σ-algebra. Then for all times `t_1 ≤ ⋯ ≤ t_n` and every bounded measurable
`F : [0, 1]^n → ℝ`,

`μ[1_{τ < ∞} F(X_{τ + t_1}, …, X_{τ + t_n}) | ℱ_τ] = 1_{τ < ∞} ∫ F dQ_{0, t}(X_τ, ·)` `μ`-almost
everywhere,

where `Q_{0, t}` is the
[finite-dimensional kernel](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/finite-chain-kernel.md)
of `κ` at the times `t = (t_1, …, t_n)`.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1 and Thm. 2.7.
- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999), ch.
  III, §1 and §3.
