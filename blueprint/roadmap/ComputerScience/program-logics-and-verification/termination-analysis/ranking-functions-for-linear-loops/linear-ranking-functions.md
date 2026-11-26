# Linear ranking functions

An affine function $\rho(x) = \vec\lambda \cdot x + \lambda_0$ on $\mathbb{Q}^n$, with $\vec\lambda \in \mathbb{Q}^n$ and $\lambda_0 \in \mathbb{Q}$, is a *linear ranking function* (LRF) for a set $T \subseteq \mathbb{Q}^{2n}$ of transitions if every $x'' = (x, x') \in T$ satisfies

$$\rho(x) \ge 0 \qquad\text{and}\qquad \rho(x) - \rho(x') \ge 1 .$$

It is an LRF for the rational [linear-constraint loop](linear-constraint-loops.md) with transition polyhedra $Q_1, \dots, Q_k$ if it is an LRF for each $Q_i$, and for the corresponding integer loop if it is an LRF for each $I(Q_i)$. The existence of an LRF implies that the loop terminates from every initial state; the converse fails. Requiring a decrease of at least $\delta$ for some $\delta > 0$ instead of $1$ gives the same existence problem. The decision problems $\mathrm{LinRF}(\mathbb{Q})$ and $\mathrm{LinRF}(\mathbb{Z})$ ask, for a multipath loop, whether it has an LRF as a rational loop, respectively as an integer loop.

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 2.3, Definitions 2.9 and 2.10.
