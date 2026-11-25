# The central-cut matrix is positive definite

For $n \ge 2$, a positive definite $A$ and $c \ne 0$, the [matrix after the step](next-matrix.md) $A'$ is positive definite, so $E(a', A')$ is again an ellipsoid. Its [inverse](next-matrix-inv.md) $\frac{n^2-1}{n^2}\bigl(A^{-1} + \frac{2}{n-1} \frac{c c^\top}{c^\top A c}\bigr)$ is a positive multiple of a positive definite matrix plus a positive semidefinite one, and $\det A' > 0$ by [the determinant formula](det-next-matrix.md), so $A' = (A'^{-1})^{-1}$ is positive definite.
