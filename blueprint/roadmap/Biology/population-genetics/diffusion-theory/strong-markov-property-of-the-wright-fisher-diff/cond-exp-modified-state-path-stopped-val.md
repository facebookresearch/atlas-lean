# Whole-path strong Markov property of the neutral realization

For every `x ∈ [0, 1]`, let `X` be the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md) of
the neutral Wright–Fisher process started at `x`, under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
with its [natural filtration](../neutral-wright-fisher-martingale-problem/natural-filtration.md)
`(ℱ_t)`, and let `τ` be an `(ℱ_t)`-stopping time with values in `[0, ∞]`. Then for every bounded
measurable `F` on the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md),

`E_x[1_{τ < ∞} F((X_{τ + u})_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F dP_{X_τ}` almost surely,

where `E_x` is the expectation under `P_x`. No Markov hypothesis is needed: the realization is
Markov
([Markov property of the realization](../neutral-wright-fisher-martingale-problem/cond-exp-modified-process-eq-wf-semigrou.md)).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986),
  ch. 4, Thm. 2.7, and ch. 10.
