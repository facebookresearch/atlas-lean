# Distance to the nearest singular operator

On a nonzero finite-dimensional inner product space (for instance $\mathbb{C}^n$ with the 2-norm), if $A$ is invertible, then the smallest $\|E\|$ such that $A - E$ is singular is $1/\|A^{-1}\|$. Dividing by $\|A\|$,

$$\min\left\{\frac{\|E\|}{\|A\|} : A - E \text{ singular}\right\} = \frac{1}{\kappa(A)},$$

so the condition number is the reciprocal of the relative distance from $A$ to the singular matrices (J. W. Demmel, Math 221 Lecture 3 notes, UC Berkeley, 2024, proved there with the SVD: the distance is the smallest singular value $\sigma_{\min}(A) = 1/\|A^{-1}\|_2$). The space must be nonzero, since on the zero space every operator is invertible.

**Proof.** If $\|E\| < 1/\|A^{-1}\|$, then $A - E$ is invertible. Conversely, take a unit vector $y$ with $\|A^{-1}y\| = \|A^{-1}\|$ (it exists by compactness of the unit sphere) and $x = A^{-1}y$; the rank-one $E = y\,x^*/\|x\|^2$ has $\|E\| = 1/\|A^{-1}\|$ and $(A - E)x = y - y = 0$.

## Informally uses

- [Small perturbations of an invertible element stay invertible](is-unit-sub.md): the lower bound.
