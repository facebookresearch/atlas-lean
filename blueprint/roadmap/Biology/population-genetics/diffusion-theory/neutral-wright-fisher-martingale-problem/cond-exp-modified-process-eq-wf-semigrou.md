# Markov property of the neutral Wright–Fisher realization

For every `x ∈ [0, 1]`, all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,

`E_x[g(X_t) | ℱ_s] = (T_{t - s} g)(X_s)` almost surely,

where `X` is the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md)
started at `x` (with values in `[0, 1]`), `E_x` the expectation under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
`(ℱ_t)` the [natural filtration](natural-filtration.md) of `X` and `T` the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, §1, (1.1) and Thm. 1.1: a process whose finite-dimensional laws are built from a transition
  function is Markov with respect to its natural filtration.
