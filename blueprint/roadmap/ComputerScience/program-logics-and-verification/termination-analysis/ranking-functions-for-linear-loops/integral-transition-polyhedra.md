# Integral transition polyhedra

Let $Q$ be the transition polyhedron of an SLC [linear-constraint loop](linear-constraint-loops.md), and suppose $Q$ is *integral*, that is, $Q$ is the convex hull of its integer points $I(Q)$. Then an affine function $\rho$ is a [linear ranking function](linear-ranking-functions.md) for $Q$ if and only if it is one for $I(Q)$. Hence on loops with integral transition polyhedra, $\mathrm{LinRF}(\mathbb{Z})$ and $\mathrm{LinRF}(\mathbb{Q})$ have the same answer. One direction holds because $I(Q) \subseteq Q$; for the other, both conditions $\rho(x) \ge 0$ and $\rho(x) - \rho(x') \ge 1$ are linear inequalities in $x''$, so they pass from integer points to their convex combinations.

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 4, Lemma 4.1.
