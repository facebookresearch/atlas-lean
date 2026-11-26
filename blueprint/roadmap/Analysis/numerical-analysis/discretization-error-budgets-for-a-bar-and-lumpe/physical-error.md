# Physical error of the P1 bar reconstruction

Let $P$ be a partition $0 = \xi_0 < \xi_1 < \dots < \xi_n = 1$ of $[0,1]$ and $I_P$ its nodal interpolant (the continuous piecewise linear function, constant outside $[0,1]$, that agrees with a given function at the nodes). For real $EA$, $L$, $q$, the physical error is $e(x) = u(x) - u_h(x)$, where

$$u(x) = \frac{q\, x (L - x)}{2\,EA}$$

and $u_h(x) = \alpha\,(I_P \hat u)(x/L)$ with $\alpha = \frac{q L^2}{2\,EA}$ and $\hat u(\xi) = \xi(1-\xi)$.

Real division by zero is $0$, so the formula is defined for all real inputs: for $EA = 0$ both $u$ and $u_h$ are $0$, and for $L = 0$ the reconstruction $u_h$ is $0$ while $u(x) = -q x^2/(2\,EA)$. For $L > 0$ and $EA > 0$, $u$ is the exact displacement of the fixed-fixed bar of length $L$ and axial rigidity $EA$ under the uniform load $q$, and $e$ is the error of the reconstruction. At zero rigidity the balance reduces to $0 = q$: no solution exists for nonzero load; at zero load the zero function is a solution, but the balance no longer determines the displacement.
