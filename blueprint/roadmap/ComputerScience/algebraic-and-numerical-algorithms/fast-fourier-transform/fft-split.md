# Even–odd split for the FFT

For a commutative ring $R$, a natural number $m$ and a vector
$x = (x_0, \dots, x_{2m-1}) \in R^{2m}$, the split returns the pair of vectors
$(x_0, x_2, \dots, x_{2m-2})$ and $(x_1, x_3, \dots, x_{2m-1})$ in $R^m$ of the entries of $x$ at
even and at odd indices, in order, at a time cost of $4m$ (the charged reads and writes).
