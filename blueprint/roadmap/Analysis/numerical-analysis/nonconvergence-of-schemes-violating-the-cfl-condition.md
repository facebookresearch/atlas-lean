# Nonconvergence of schemes violating the CFL condition

For the advection equation $q_t + a q_x = 0$ and an explicit scheme of stencil radius $r$ with $\lvert a \rvert \Delta t/\Delta x > r$ and the
ratio $\Delta t/\Delta x = \lambda$ fixed, fix a point $(x, t)$ with $t > 0$. Let $q_0$ be smooth and let $\varphi$ be a smooth bump supported in an
interval around $x - at$ that is disjoint from $[x - r t/\lambda, x + r t/\lambda]$, with $\varphi(x - at) \ne 0$. Then, on every sufficiently fine grid, at the grid point $(x_j, t_n)$ nearest to $(x, t)$, the scheme gives the same value for the pointwise samples of $q_0$ and of $q_0 + \varphi$, while the exact solutions
at $(x, t)$ differ by $\varphi(x - at)$; hence the scheme cannot converge to the exact solution for both initial data.

## Proof

After $n$ steps, with $t_n = n \Delta t$, the computed value at index $j$ depends only on initial indices within $rn$ of $j$, that is on samples in $[x_j - r t_n/\lambda, x_j + r t_n/\lambda]$. As $x_j \to x$ and $t_n \to t$ this interval approaches $[x - r t/\lambda, x + r t/\lambda]$, which has positive distance from the support of $\varphi$, so on fine grids $\varphi$ vanishes at all these samples. The exact solution is $q_0(x - at)$ or
$q_0(x - at) + \varphi(x - at)$, and $\lvert x - at - x \rvert = \lvert a \rvert t > r t/\lambda$ puts $x - at$ outside that window.

## Depends on

- [CFL condition: numerical domain of dependence must contain the true one](cfl-condition-numerical-domain-of-dependence-must-contain-th.md)

## Sources

- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press, 2002, Section 4.4 (the CFL condition as a necessary condition for convergence); AMath 574 lecture notes, slides "The CFL Condition" and "Numerical domain of dependence". <https://faculty.washington.edu/rjl/classes/hyperbolic2013/am574w2011/am574lecture5nup3.pdf>
