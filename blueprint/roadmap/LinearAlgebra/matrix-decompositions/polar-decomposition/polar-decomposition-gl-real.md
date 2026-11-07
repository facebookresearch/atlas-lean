# Polar decomposition of invertible real matrices

Let $A$ be a real square matrix with rows
and columns indexed by a finite set, and suppose $\det A \ne 0$. Then there are an orthogonal
matrix $O$ and a positive-definite symmetric matrix $S$ with $A = OS$, and they are unique: if
$O'$ is orthogonal, $S'$ is positive-definite symmetric and $A = O'S'$, then $O' = O$ and
$S' = S$.

Proof: take $S$ to be the positive-definite square root of $A^{\mathsf{T}} A$ and $O = AS^{-1}$,
the construction in Wikipedia, "Polar decomposition".

## Sources

- Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space / Endomorphisms / polar decompositions in GL(n, ℝ); R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 7.3.1.
