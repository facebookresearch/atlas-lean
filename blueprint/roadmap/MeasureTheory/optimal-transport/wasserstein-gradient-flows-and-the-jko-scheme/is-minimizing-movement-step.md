# Minimizing-movement (JKO) step

Let $(X, d)$ be a (pseudo)metric space, $F : X \to \mathbb{R}$ a functional and $h$ a time step. A
point $y$ is a *minimizing-movement step* from $x$ if it minimizes

$$z \mapsto \tfrac12 d(x, z)^2 + h F(z)$$

over $X$. This is the implicit Euler scheme for the gradient flow of $F$ written with the distance
only: in a Hilbert space with $F$ differentiable, a minimizer satisfies $y = x - h \nabla F(y)$.

Jordan, Kinderlehrer and Otto introduce the scheme (their (13)) with $X$ the probability densities
on $\mathbb{R}^n$ with finite second moment, $d$ the [quadratic Wasserstein distance](../wasserstein-distances/wasserstein.md) and
$F$ the free energy; the definition keeps their normalization $\tfrac12 d^2 + hF$ rather than
$d^2/(2h) + F$, which is equivalent for $h > 0$.

## Background

- [JKO step](is-jkostep.md): the scheme on probability densities with the Wasserstein distance.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, scheme (13).
