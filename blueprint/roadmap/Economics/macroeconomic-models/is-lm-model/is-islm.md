# Linear IS–LM equilibrium conditions

Output `Y` and the interest rate `r` solve the linear IS–LM system with
parameters `b`, `h`, `k` and exogenous `A`, `M` when

IS: `Y + b * r = A` and LM: `k * Y - h * r = M`.

Here `b` is the interest sensitivity of demand, `h` the interest sensitivity of
money demand, `k` the income sensitivity of money demand, `A` autonomous spending
(the IS intercept) and `M` the real money supply (the LM intercept). The
definition imposes no sign on `b`, `h` and `k`; the results on this model assume
all three positive. In matrix form the system matrix is `[[1, b], [k, -h]]`, with
determinant `-(h + b * k)`.
