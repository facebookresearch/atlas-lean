# Occupation identity until absorption persists under uniform limits

Let `μ` be a probability measure, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a solution of the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with `σ = 0` with respect to `(ℱ_t)` and `μ`, with `X_0 = x` `μ`-almost surely, where `x ∈ [0, 1]`,
and let `τ` be the
[absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) of `X`.
For every `n`, let `g_n` be a continuous real function and `u_n` a twice continuously differentiable
real function with `(L_0 u_n)(y) = -g_n(y)` for every real `y`, where `L_0` is the neutral
[backward generator](../wright-fisher-diffusion/generator.md), and `u_n(0) = u_n(1) = 0`. Let `g` be
a continuous real function and `u` a real function such that `u_n → u` and `g_n → g` uniformly on
`[0, 1]`. Then `∫₀^τ g(X_s) ds` is integrable and

`E[∫₀^τ g(X_s) ds] = u(x)`,

where `E` is the expectation under `μ`. The limit `u` need not be twice differentiable. With
constant sequences it gives the
[expected occupation integral until absorption, from L₀u = −g](integral-absorption-time-of-generator-eq.md).
The condition `x ∈ [0, 1]` also follows from `X_0 = x` almost surely, since `X` takes values in
`[0, 1]` and `μ` is a probability measure.
