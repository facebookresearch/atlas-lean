# Linear IS–LM equilibrium conditions

The linear IS-LM system. Parameters: `b > 0` is the interest sensitivity of
investment/demand, `h > 0` the interest sensitivity of money demand, `k > 0` the income
sensitivity of money demand. Variables: `Y` output, `r` interest rate. Exogenous:
`A` autonomous spending (IS intercept), `M` real money supply (LM intercept).
IS: `Y + b * r = A`. LM: `k * Y - h * r = M`.
In matrix form the system matrix is `[[1, b], [k, -h]]` with determinant `-(h + b * k)`.
