# Upper-triangular matrix of a two-variable policy model

The two-variable linear policy model has state evolving by `x(t + 1) = A x(t) + c`
with the upper-triangular matrix `A = [[a, b], [0, d]]` (rows listed in order), for real
`a`, `b` and `d`. The diagonal entries `a` and `d` are the policy feedback
coefficients and the eigenvalues of `A`; the off-diagonal entry `b` couples the
second state variable into the first equation.
