# A missing-ray cell in a matrix with no zero row: a two-by-two example

For the real ray-length matrix `A` with rows `(1, 0)` and `(1, 0)`, both rays cross only the first
cell, so the second column is zero although no row is: `A (0, 1) = (0, 0)` and
`A (1, 0) = (1, 1)`. Perturbing the slowness of the second cell leaves both travel times
unchanged, while a unit perturbation of the first cell is seen by both rays.
