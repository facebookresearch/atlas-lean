# A computed temperature after ten steps lies within its error budget

For real numbers `C > 0`, `G > 0`, `T_amb` and `Δ`, a real sequence `X` with `X_0 = T_amb + Δ` whose
terms follow [Euler steps](bath-euler-step.md) of size `τ / 10`, and every real sequence `Y`,
`|Y_10 - T(τ)|` is at most the [ten-step error budget](ten-step-error-budget.md) of `Y`, where `T`
is the exact [trajectory](bath-trajectory.md).
