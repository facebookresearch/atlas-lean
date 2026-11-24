# The endpoint of an accepted trace is the tenth Euler iterate

For real numbers `C > 0` (heat capacity) and `G > 0` (bath conductance), `T_amb` and `Δ`, and every
list `y` accepted by the [trace checker](check-thermal-trace.md), the [endpoint](trace-endpoint.md)
`T_amb + Δ y_10` equals the result of ten
[explicit Euler steps](../../../Analysis/numerical-analysis/error-budgets-for-discretized-bar-and-heat-bath/bath-euler-step.md)
of size `τ / 10`, with `τ = C / G` the
[thermal time constant](../../../Analysis/numerical-analysis/error-budgets-for-discretized-bar-and-heat-bath/thermal-time-constant.md),
started at `T_amb + Δ`.
