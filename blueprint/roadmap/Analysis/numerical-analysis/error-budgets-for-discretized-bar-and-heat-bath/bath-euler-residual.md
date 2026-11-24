# Residual of a computed temperature sequence in the Euler recurrence

For real numbers `C`, `G` and `T_amb`, a real sequence `Y` and an index `j`, the residual is
`η_j = Y_{j+1} - S(Y_j)`, where `S` is the [Euler step](bath-euler-step.md) of size `τ / 10`,
`τ = C / G`: the amount by which the computed step `j` misses one exact Euler step. With the
convention `a / 0 = 0`, when `C = 0` or `G = 0` the step leaves `Y_j` unchanged and
`η_j = Y_{j+1} - Y_j`; the intended domain is `C > 0` and `G > 0`.
