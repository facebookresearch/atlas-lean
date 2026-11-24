# An ellipsoid is the image of the unit ball

For a positive definite $n \times n$ matrix $A$, $E(0, A) = A^{1/2}\, E(0, I)$, where
$E(a, A) = \{x : (x - a)^\top A^{-1} (x - a) \le 1\}$ and $A^{1/2}$ is the positive definite square
root of $A$. Indeed $A^{-1} = A^{-1/2} A^{-1/2}$ with $A^{-1/2}$ symmetric, so
$x^\top A^{-1} x = \lVert A^{-1/2} x\rVert^2$, and $x \in E(0, A)$ exactly when $A^{-1/2} x$ lies in
the unit ball. Goemans writes $A = B^\top B$ for some $B$; the square root is the symmetric choice
of $B$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, Definition 7.1 and the remark after it.
