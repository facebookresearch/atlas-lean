# Last Row mul last Column swap distinct

Row-before-column swap for distinct indices `i ≠ j` with
`i < n` and `j < n`. The product `x n j b * x i n a` has exactly
one adjacent row-before-column inversion; swapping it introduces
the single correction `x i j (-(a*b))`, which lies in
`finiteStage n` via `x_mem_finiteStage`. This is the atomic step
for the normal-form inversion-removal induction.
