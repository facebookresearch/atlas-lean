# Representation of a sublinear expectation as a maximum of linear expectations

Let $\mathcal{H}$ be a linear space of real functions on a set $\Omega$, let $\mathbb{E}$ be a
[sublinear expectation](is-sublinear-expectation.md) on $\mathcal{H}$ and let $X \in \mathcal{H}$.
Then $\mathbb{E}[X]$ is the largest value of $f(X)$ over the linear functionals $f$ on
$\mathcal{H}$ that are dominated by $\mathbb{E}$, monotone and constant preserving (the linear
expectations dominated by $\mathbb{E}$), and the maximum is attained:
$\mathbb{E}[X] = \max_\theta \mathbb{E}_\theta[X]$.

## Background

- [Coherent risk measure](../coherent-risk-measures/is-coherent-risk-measure.md): through $\rho(X) = \mathbb{E}[-X]$, the
  representation is the robust representation $\rho(X) = \max_Q \mathbb{E}_Q[-X]$ of a coherent
  risk measure by a set of (finitely additive) scenario measures (Artzner, Delbaen, Eber and
  Heath, 1999; Delbaen, 2002), which Peng's Notes to Chapter I relate to this theorem.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Theorem 2.1.
