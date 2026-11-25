# Lax-Wendroff theorem on conservative schemes

This node covers the Lax-Wendroff theorem. Let $f : \mathbb{R} \to \mathbb{R}$ be continuous and let a scheme for $u_t + f(u)_x = 0$ be in
conservation form, $U_j^{n+1} = U_j^n - \lambda\big(F(U_{j-p}^n, \dots, U_{j+q}^n) - F(U_{j-p-1}^n, \dots, U_{j+q-1}^n)\big)$ with fixed
$\lambda = \Delta t/\Delta x$, whose numerical flux $F$ is Lipschitz and consistent, $F(u, \dots, u) = f(u)$. Suppose that along a sequence
$\Delta x \to 0$ the piecewise-constant approximations are uniformly bounded and converge in $L^1_{\mathrm{loc}}(\mathbb{R} \times [0, \infty))$ to
a function $u$, with initial data converging in $L^1_{\mathrm{loc}}(\mathbb{R})$ to $u_0$. Then $u$ is a weak solution of the conservation law with
initial data $u_0$.

## Expansion

A good expansion multiplies the scheme by a test function, sums by parts using the conservation form, and passes to the limit
using consistency and the Lipschitz bound. Entropy consistency, which additionally selects the entropy solution, and convergence proofs for
monotone schemes are separate nodes.

## Sources

- P. D. Lax and B. Wendroff, Systems of conservation laws, *Communications on Pure and Applied Mathematics* 13 (1960) 217-237.
- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press, 2002.
