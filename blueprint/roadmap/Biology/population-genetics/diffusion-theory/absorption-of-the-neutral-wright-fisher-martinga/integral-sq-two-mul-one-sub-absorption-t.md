# Expected integral of squared heterozygosity until absorption

Let `μ` be a probability measure, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a solution of the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with `σ = 0` with respect to `(ℱ_t)` and `μ`, with `X_0 = x` `μ`-almost surely, and let `τ` be the
[absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) of `X`.
Then `∫₀^τ (2 X_s (1 - X_s))² ds` is integrable and

`E[∫₀^τ (2 X_s (1 - X_s))² ds] = (2/3) x (1 - x) (1 + x - x²)`,

where `E` is the expectation under `μ` and time is in units of `2N` generations. This is the
expected occupation integral of the squared heterozygosity, not the second moment of the accumulated
heterozygosity.
