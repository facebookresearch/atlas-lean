# Determinant after a central-cut step

If $A$ is positive definite and $c \ne 0$, then the [matrix after the step](next-matrix.md) satisfies

$$
\det A' = \Bigl(\frac{n^2}{n^2-1}\Bigr)^{n} \, \frac{n-1}{n+1} \, \det A .
$$

By the matrix determinant lemma, $\det(A - \beta\, b b^\top) = \det A \,(1 - \beta\, b^\top A^{-1} b)$, and [$b^\top A^{-1} b = 1$](cut-direction-inv-norm.md); with $\beta = 2/(n+1)$ the second factor is $(n-1)/(n+1)$, and the scalar $n^2/(n^2-1)$ contributes its $n$-th power. The statement uses real division, so for $n = 1$ both sides are $0$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, equation (5) and the proof of Lemma 7.1 (there by reduction to the unit ball).
