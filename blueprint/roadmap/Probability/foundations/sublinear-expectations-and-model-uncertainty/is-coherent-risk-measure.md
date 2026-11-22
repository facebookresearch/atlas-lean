# Coherent risk measure

Let $\mathcal{H}$ be a linear space of real functions on a set $\Omega$. A functional
$\rho$ on real functions on $\Omega$ is a coherent risk measure on $\mathcal{H}$ if $\mathcal{H}$
contains the constants and: $\rho(X) \le \rho(Y)$ whenever $Y \le X$ in $\mathcal{H}$;
$\rho(1) = -1$ and $\rho(-1) = 1$; $\rho(X + Y) \le \rho(X) + \rho(Y)$ for $X, Y \in \mathcal{H}$;
and $\rho(cX) = c\, \rho(X)$ for $X \in \mathcal{H}$ and $c \ge 0$. These are the four properties
that Peng proves for the risk measure $\rho_A(X) = \inf\{m : m + X \in A\}$ of a coherent
acceptable set $A$ (Proposition 5.5 and Definition 5.4 of the source).

## Background

- [Sublinear expectation](is-sublinear-expectation.md): Peng's point of view, in which a coherent
  risk measure is the sublinear expectation $\mathbb{E}[X] = \rho(-X)$ of the loss.

## Sources

- P. Artzner, F. Delbaen, J.-M. Eber and D. Heath, *Coherent measures of risk*, Mathematical
  Finance 9 (1999), 203–228.
- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Definition 5.4 and Proposition 5.5.
