# Strong Markov property of the realization, given its Markov property

For every `x ∈ [0, 1]`, let `X` be the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md) of
the neutral Wright–Fisher process started at `x`, under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
with its [natural filtration](../neutral-wright-fisher-martingale-problem/natural-filtration.md)
`(ℱ_t)`. Suppose that `X` is Markov with respect to `(ℱ_t)` with the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md)
`T`: for all times `0 ≤ s ≤ t` and every continuous `g : [0, 1] → ℝ`,
`E_x[g(X_t) | ℱ_s] = (T_{t - s} g)(X_s)` almost surely. Then for every `(ℱ_t)`-stopping time `τ`
with values in `[0, ∞]`, every time `t ≥ 0` and every continuous `g : [0, 1] → ℝ`,

`E_x[1_{τ < ∞} g(X_{τ + t}) | ℱ_τ] = 1_{τ < ∞} (T_t g)(X_τ)` almost surely.

The hypothesis always holds
([Markov property of the realization](../neutral-wright-fisher-martingale-problem/cond-exp-modified-process-eq-wf-semigrou.md)),
which gives the [unconditional statement](cond-exp-modified-state-stopped-value-ad.md).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, Thm. 2.7, and ch. 10.
