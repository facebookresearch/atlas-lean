# Expected occupation integral until absorption, from L₀u = −g

Let `μ` be a probability measure, `(ℱ_t)_{t ≥ 0}` a filtration and `X` a solution of the
[martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
with `σ = 0` with respect to `(ℱ_t)` and `μ`, with `X_0 = x` `μ`-almost surely, and let `τ` be the
[absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) of `X`.
Let `g` be a continuous real function and `u` a twice continuously differentiable real function with
`(L_0 u)(y) = -g(y)` for every real `y`, where `L_0` is the neutral
[backward generator](../wright-fisher-diffusion/generator.md), and `u(0) = u(1) = 0`. Then
`∫₀^τ g(X_s) ds` is integrable and

`E[∫₀^τ g(X_s) ds] = u(x)`,

where `E` is the expectation under `μ` and time is in units of `2N` generations.
