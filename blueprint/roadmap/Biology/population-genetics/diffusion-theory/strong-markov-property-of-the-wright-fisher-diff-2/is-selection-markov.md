# Selection diffusion that is Markov for a kernel family

Let `σ` be a real number, `κ = (κ_t)_{t ≥ 0}` a family of kernels on `[0, 1]`, `(ℱ_t)_{t ≥ 0}` a
filtration on a measurable space `Ω` and `μ` a measure on `Ω`. A real process `X` is a Wright–Fisher
diffusion with scaled selection coefficient `σ = 2Ns`, Markov for `κ`, if it solves the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with selection `σ` with respect to `(ℱ_t)` and `μ`, and for all times `0 ≤ s ≤ t` and every
continuous `g : [0, 1] → ℝ`, `μ[g(X_t) | ℱ_s] = ∫ g(y) κ_{t - s}(X_s, dy)` `μ`-almost everywhere
(`X` takes values in `[0, 1]`). The kernels are not determined by `σ`: they are part of the data.
Neither `μ` finite nor the kernels Markov is required: the conditional expectation is taken to be
`0` for a non-integrable input or when `μ` is not σ-finite on `ℱ_s`, and the kernel integral is `0`
when `g` is not integrable against `κ_{t - s}(X_s, ·)`. For a finite `μ` and Markov kernels both are
the usual objects.
