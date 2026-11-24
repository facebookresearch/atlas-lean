# The endpoint of an accepted trace is within a tenth of the excess

For real numbers `C > 0` and `G > 0`, `T_amb` and `Δ`, and every list `y` accepted by the
[trace checker](check-thermal-trace.md), the [endpoint](trace-endpoint.md) differs from the
[exact bath trajectory](../../../Analysis/numerical-analysis/error-budgets-for-discretized-bar-and-heat-bath/bath-trajectory.md)
`T_amb + Δ exp(-t / τ)` at `t = τ = C / G` by at most `|Δ| / 10`.
