# Uniform-limit occupation identity for the neutral realization

For `x ∈ [0, 1]`, let `X` be the
[continuous realization](../construction-of-the-neutral-wright-fisher-diffus/modified-process.md) of
the neutral Wright–Fisher process started at `x`, under the
[canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/raw-measure.md) `P_x`,
and `τ` the
[absorption time](../fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md) of `X`.
For every `n`, let `g_n` be a continuous real function and `u_n` a twice continuously differentiable
real function with `(L_0 u_n)(y) = -g_n(y)` for every real `y`, where `L_0` is the neutral
[backward generator](../wright-fisher-diffusion/generator.md), and `u_n(0) = u_n(1) = 0`. Let `g` be
a continuous real function and `u` a real function such that `u_n → u` and `g_n → g` uniformly on
`[0, 1]`. Then `∫₀^τ g(X_s) ds` is integrable under `P_x` and its expectation is `u(x)`.
