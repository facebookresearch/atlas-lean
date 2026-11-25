# Inverse of the matrix after a central-cut step

For $n \ge 2$, a positive definite $A$ and $c \ne 0$, the [matrix after the step](next-matrix.md) has inverse

$$
A'^{-1} = \frac{n^2 - 1}{n^2} \Bigl( A^{-1} + \frac{2}{n - 1} \, \frac{c c^\top}{c^\top A c} \Bigr).
$$

This is the Sherman–Morrison formula for the rank-one update $A - \beta\, b b^\top$ with $\beta = 2/(n+1)$ and $b = A c / \sqrt{c^\top A c}$: since $A^{-1} b = c/\sqrt{c^\top A c}$ and $b^\top A^{-1} b = 1$, the correction is $\frac{\beta}{1 - \beta} A^{-1} b b^\top A^{-1} = \frac{2}{n-1} \frac{c c^\top}{c^\top A c}$. The proof checks $A' \cdot A'^{-1} = I$ on the basis vectors.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, equation (5) (the matrix $A'$; the inverse is not written there).
