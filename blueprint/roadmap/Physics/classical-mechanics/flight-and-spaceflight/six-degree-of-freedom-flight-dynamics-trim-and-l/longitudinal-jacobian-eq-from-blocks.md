# The trim Jacobian is block diagonal

The [longitudinal Jacobian](longitudinal-jacobian.md) `A` is the direct sum of the translational
block `diag(−1, −1)` on the coordinates `(x, z)` and the pitch block `[[0, 1], [−1, −2]]` on
`(θ, q)`: with the first two coordinates forming the first block and the last two the second,

`A = [[diag(−1, −1), 0], [0, [[0, 1], [−1, −2]]]]`.
