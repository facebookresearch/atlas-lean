# Conditional expectation given a partition

For a real function $p$ on a finite set $\Omega$ (a prior), a partition $\mathcal P$ and a real function $g$, the
conditional expectation of $g$ given $\mathcal P$ at $\omega$ is

$$\mathbb E[g \mid \mathcal P](\omega) = \frac{\sum_{x \in P(\omega)} p(x)\, g(x)}{\sum_{x \in P(\omega)} p(x)},$$

the average of $g$ over the cell of $\omega$, with the convention $x / 0 = 0$: on a null cell its value
is $0$.

## Background

- [Information cell as a finset](../common-knowledge-and-the-agreement-theorem/cell-finset.md):
  the cell summed over.

## Sources

- R. J. Aumann, "Correlated equilibrium as an expression of Bayesian rationality", Econometrica 55(1) (1987), 1–18, footnote 8 (conditional expectation $E(x \mid \mathcal P^i)$ as the random variable whose value at $\omega$ is $E(x \mid P)$, $P$ the cell of $\omega$).
