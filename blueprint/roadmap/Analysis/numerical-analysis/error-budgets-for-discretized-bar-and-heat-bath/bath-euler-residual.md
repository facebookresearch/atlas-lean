# Residual of a computed temperature sequence in the Euler recurrence

For real numbers `C`, `G` and `T_amb`, a real sequence `Y` and an index `j`, the residual is
`η_j = Y_{j+1} - S(Y_j)`, where `S` is the [Euler step](bath-euler-step.md) of size `τ / 10`,
`τ = C / G`: the amount by which the computed step `j` misses one exact Euler step.
