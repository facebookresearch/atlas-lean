# The LP matrix acts through the free part

For the data of a dispatch problem and every LP point `x = (u, w)`, with first and second
coordinate blocks `u` and `w`, `A x = F (u - w)`, where
`A = [F, -F]` is the [LP constraint matrix](lp-matrix.md) and `F` the
[constraint matrix on generation and angles](free-constraint-matrix.md).
