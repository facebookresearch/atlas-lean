# Minimizing-movement scheme

Let $(X, d)$ be a pseudometric space, $F : X \to \mathbb{R}$ a functional and $h$ a real time step. A point $y$
is a minimizing-movement step from $x$ when it minimises $z \mapsto \frac12 d(x, z)^2 + h F(z)$ over
$X$, and a sequence $(\rho_k)_{k \ge 0}$ solves the minimizing-movement scheme when each
$\rho_{k+1}$ is a minimizing-movement step from $\rho_k$.

## Idea

The scheme is the implicit Euler method for the gradient flow of $F$, written with the distance
only: in a Hilbert space, for differentiable $F$, a step satisfies $y = x - h \nabla F(y)$. It gives
a meaning to gradient flows in metric spaces without a differential structure, such as the
Wasserstein space, where the Jordan–Kinderlehrer–Otto scheme is an instance. Its basic estimates use
only the metric. For $h > 0$ a step does not increase $F$, since it beats staying at $x$. Summing the
one-step inequalities gives the discrete energy inequality
$\frac12 \sum_{k=0}^{n-1} d(\rho_k, \rho_{k+1})^2 \le h (F(\rho_0) - F(\rho_n))$, and the Cauchy–Schwarz
inequality turns it into a Hölder-$\frac12$ bound in time. On a proper metric space, steps and
sequences exist when $h > 0$ and $F$ is lower semicontinuous and bounded below.

## Statements

- [Minimizing-movement (JKO) sequence](is-minimizing-movement.md)
- [Minimizing-movement (JKO) step](is-minimizing-movement-step.md): one step of the scheme.
- [Existence of a JKO step on a proper metric space](exists-is-minimizing-movement-step.md): existence of a step.
- [Existence of a JKO sequence on a proper metric space](exists-is-minimizing-movement.md): existence of the scheme.
- [The JKO step decreases the functional](le.md): a basic estimate: a step does not increase $F$ when $h > 0$.
- [The functional decreases along the JKO scheme](antitone.md): the same along the whole scheme.
- [One-step energy inequality of the JKO scheme](energy-le.md): the one-step energy inequality.
- [Discrete energy inequality of the JKO scheme](energy-sum-le.md): the energy inequality summed along the scheme.
- [Discrete energy inequality, multiplied form](sum-add-le.md): the summed inequality multiplied by $h$, which holds for every real $h$ and is equivalent to it for $h > 0$.
- [Hölder-½ estimate of the JKO scheme](dist-sq-le.md): the Hölder-$\frac12$ estimate in time, from the summed inequality.
- [Uniform Hölder-½ bound of the JKO scheme](dist-sq-le-of-le.md): a uniform form of the Hölder estimate.
- [Tails of a minimizing-movement sequence](shift.md): the tail of a scheme is a scheme, used to restart estimates.

## Sources

- R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998).
