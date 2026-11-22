# Linear Policy Matrix

A fixed 2-variable linear policy model: the state evolves by
`x_{t+1} = A x_t + c` where `A` is the upper-triangular matrix below.
The diagonal entries `a` and `d` are the policy feedback coefficients
(the eigenvalues, see the two eigenvector equations below); the
off-diagonal entry `b` couples the second state variable into the first
equation. Upper-triangular form is the frozen contract: it makes the
eigenvalues explicitly readable off the diagonal while keeping a
nontrivial coupling term.
