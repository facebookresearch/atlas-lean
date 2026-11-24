# Three-term ten-step error budget

For `C, G > 0`, the exact Euler recurrence `X` at
`dt = τ / 10` from `X 0 = T_amb + Δ` and any computed sequence `Y`, the computed temperature
after ten steps is within the budget of the exact trajectory at `τ`: the propagated initial error,
the weighted actual residuals and the truncation term `|Δ| / 10`.
