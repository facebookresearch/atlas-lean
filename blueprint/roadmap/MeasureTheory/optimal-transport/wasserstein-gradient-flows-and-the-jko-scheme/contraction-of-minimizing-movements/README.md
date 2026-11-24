# Discrete exponential stability of minimizing movements

Let $H$ be a real inner product space and $F : H \to \mathbb{R}$ a $\lambda$-convex functional:
$F((1-t)a + tb) \le (1-t)F(a) + tF(b) - t(1-t)\frac{\lambda}{2}\|a - b\|^2$ for $t \in [0, 1]$. Let
$h > 0$ with $1 + \lambda h > 0$. Then any two minimizing-movement sequences $(\rho^1_k)$ and
$(\rho^2_k)$ for $F$ with time step $h$ satisfy, for every $k$,

$$(1 + \lambda h)^k \, \|\rho^1_k - \rho^2_k\| \le \|\rho^1_0 - \rho^2_0\|.$$

## Idea

Gradient flows of $\lambda$-convex functionals satisfy
$\|\rho^1(t) - \rho^2(t)\| \le e^{-\lambda t} \|\rho^1(0) - \rho^2(0)\|$; this is the time-discrete
version, with $(1 + \lambda h)^{-k}$ the implicit-Euler approximation of $e^{-\lambda kh}$. It is a
contraction for $\lambda > 0$ and nonexpansion for $\lambda = 0$; $\lambda < 0$ is allowed and then
the bound permits growth: for $F(x) = -x^2/2$ on $\mathbb{R}$ ($\lambda = -1$) and $h = 1/2$ the step is
$y = 2x$, which doubles distances. Each step satisfies a variational inequality,
$\langle x - y, z - y \rangle \le h(F(z) - F(y)) - h \frac{\lambda}{2}\|z - y\|^2$ for all $z$,
obtained by comparing $y$ with points on the segment towards $z$. Adding the inequalities of two
steps tested against each other and applying the Cauchy–Schwarz inequality gives the one-step
bound, which iterates. In the Wasserstein space, displacement convexity plays the role of
$\lambda$-convexity.

## Statements

- [Discrete exponential stability bound for minimizing movements](contraction-pow.md)
- [Contraction of the minimizing-movement step](contraction.md): the one-step form.
- [Variational inequality of the minimizing-movement step](inner-le.md): used in the proof.

## Background

- [Minimizing-movement scheme](../minimizing-movements/README.md): the scheme of the statement.
- [McCann's condition for displacement convexity](../../displacement-convexity/README.md): the Wasserstein analogue of $\lambda$-convexity.
