# A Poincaré inequality bounds the spectral gap

Let $S$ be a finite set, $\pi$ a probability vector on $S$ with $\pi(x) > 0$ for every $x$, and
$P$ a real $S \times S$ matrix with unit row sums in detailed balance with $\pi$:
$\pi(x) P(x, y) = \pi(y) P(y, x)$ for all $x, y$. Let $B$ be a real number such that for every
$\psi : S \to \mathbb{R}$

$$\sum_{x,y} (\psi(x)-\psi(y))^2\,\pi(x)\pi(y) \;\le\; B \sum_{x,y} (\psi(x)-\psi(y))^2\,\pi(x)P(x,y).$$

Then every real eigenvalue $\mu \ne 1$ of $P$, with a nonzero real eigenvector $f$ ($Pf = \mu f$),
satisfies $1 \le B(1-\mu)$. The eigenvectors for $\mu \ne 1$ are orthogonal to the constants in
$L^2(\pi)$, so this follows from [the version for eigenvectors orthogonal to
constants](one-le-mul-one-sub-of-poincare-of-mean-z.md). Sinclair proves Theorems 5 and 5′ this
way, with $B = \bar\rho(\Gamma)$ for canonical paths and $B = \bar\rho(f)$ for flows.

## Background

- [Sinclair's Poincaré hypothesis is a lower bound on the spectral gap](../dirichlet-forms/inv-le-spectral-gap-iff-poincare.md):
  when $B > 0$, $P$ is stochastic ($P \ge 0$ with unit row sums) and some function has nonzero
  variance, the hypothesis of this theorem is equivalent to $1/B \le \lambda$ for the spectral gap
  $\lambda$ defined variationally from the Dirichlet form (Diaconis and Saloff-Coste 1996,
  equation (1.4)).

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, Theorems 5 and 5′ and the
  variational characterisation (5).
