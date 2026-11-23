# Kimura–Ohta mean absorption time of a neutral solution

Let `μ` be a probability measure, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a solution of the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with `σ = 0` with respect to `(ℱ_t)` and `μ`, with `X_0 = x` `μ`-almost surely. Then the
[absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) `τ` of `X`
is integrable and its mean, in units of `2N` generations, is

`E[τ] = -2 (x log x + (1 - x) log (1 - x))`,

where `E` is the expectation under `μ`; here `x ∈ [0, 1]`, as `X` takes values in `[0, 1]`, and
`0 log 0 = 0`.

## Sources

- M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in a
  finite population*, Genetics 61 (1969), 763–771.
- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer
  (2004), ch. 4.
