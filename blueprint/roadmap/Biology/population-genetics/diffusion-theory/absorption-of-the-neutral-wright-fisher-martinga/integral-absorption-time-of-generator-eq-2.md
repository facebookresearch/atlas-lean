# Occupation integral until absorption for the neutral realization

For every `x ∈ [0, 1]`, let `X` be the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md) of
the neutral Wright–Fisher process started at `x`, under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
and `τ` the
[absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) of `X`.
Let `g` be a continuous real function and `u` a twice continuously differentiable real function with
`(L_0 u)(y) = -g(y)` for every real `y`, where `L_0` is the neutral
[backward generator](../wright-fisher-diffusion/generator.md), and `u(0) = u(1) = 0`. Then
`∫₀^τ g(X_s) ds` is integrable under `P_x` and its expectation is `u(x)`.
