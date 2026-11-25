# A symmetric 3×3 matrix that is not conditionally negative semidefinite

The symmetric matrix on three populations `0, 1, 2` with zero diagonal and off-diagonal entries
`D 0 1 = D 0 2 = 1` and `D 1 2 = 9`. It is not
[conditionally negative semidefinite](is-cond-neg-semidef.md): for `c = (-2, 1, 1)`, which sums to
`0`, `∑ i, ∑ j, c i * c j * D i j = 10 > 0`. Nor is it a matrix of squared Euclidean distances, as
`√9 > √1 + √1` violates the triangle inequality; so it is not
[realizable by a drift model](is-f2-realizable.md).
