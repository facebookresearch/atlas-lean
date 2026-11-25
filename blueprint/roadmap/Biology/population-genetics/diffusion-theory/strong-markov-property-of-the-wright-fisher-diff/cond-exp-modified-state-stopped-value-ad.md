# Strong Markov property of the neutral Wright–Fisher realization

For every `x ∈ [0, 1]`, let `X` be the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md) of
the neutral Wright–Fisher process started at `x`, under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
with its [natural filtration](../neutral-wright-fisher-martingale-problem/natural-filtration.md)
`(ℱ_t)`. Then for every `(ℱ_t)`-stopping time `τ` with values in `[0, ∞]`, every time `t ≥ 0` and
every continuous `g : [0, 1] → ℝ`,

`E_x[1_{τ < ∞} g(X_{τ + t}) | ℱ_τ] = 1_{τ < ∞} (T_t g)(X_τ)` almost surely,

where `E_x` is the expectation under `P_x` and `T` is the
[neutral Wright–Fisher semigroup](../wright-fisher-semigroup-and-moment-duality/wf-semigroup.md).
