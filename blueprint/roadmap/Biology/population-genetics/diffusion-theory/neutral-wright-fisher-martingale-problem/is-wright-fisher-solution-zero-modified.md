# The neutral Wright–Fisher realization solves the martingale problem

For every `x ∈ [0, 1]`, the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md)
`X` started at `x`, with its [natural filtration](natural-filtration.md) and the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
solves the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with `σ = 0`: its paths are continuous with values in `[0, 1]`, it is adapted to its natural
filtration, and for every twice continuously differentiable `f : ℝ → ℝ` the process
`f(X_t) - f(X_0) - ∫₀ᵗ X_s (1 - X_s) / 2 · f''(X_s) ds` is a martingale under `P_x`.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, Prop. 1.7.
