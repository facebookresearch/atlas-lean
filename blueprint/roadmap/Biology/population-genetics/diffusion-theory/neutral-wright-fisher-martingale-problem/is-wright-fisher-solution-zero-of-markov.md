# Neutral Wright–Fisher martingale problem from the Markov property

Let `μ` be a finite measure on a measurable space `Ω`, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a real
process with values in `[0, 1]`, continuous paths, adapted to `(ℱ_t)`, and Markov with respect to
`(ℱ_t)` with the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
`T`: for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`, the conditional expectation
under `μ` satisfies `μ[g(X_t) | ℱ_s] = (T_{t - s} g)(X_s)` `μ`-almost everywhere. Then `X` solves
the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with `σ = 0` with respect to `(ℱ_t)` and `μ`: besides the properties assumed, for every twice
continuously differentiable `f : ℝ → ℝ` the process
`f(X_t) - f(X_0) - ∫₀ᵗ X_s (1 - X_s) / 2 · f''(X_s) ds` is an `(ℱ_t)`-martingale under `μ`.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, Prop. 1.7 (Markov processes solve the martingale problem for their generator), and ch. 10.
