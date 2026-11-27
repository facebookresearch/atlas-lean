# Weak lexicographic-linear ranking functions

Let $Q_1, \dots, Q_k$ be the transition polyhedra of a multipath [linear-constraint loop](linear-constraint-loops.md), and for an affine $\rho$ write $\Delta\rho(x'') = \rho(x) - \rho(x')$ for a transition $x'' = (x, x')$. A $d$-tuple $\tau = \langle \rho_1, \dots, \rho_d \rangle$ of affine functions is a *weak lexicographic-linear ranking function* (weak LLRF) for $Q_1 \cup \dots \cup Q_k$ if every transition $x''$ in the union has an index $i \le d$ with

$$\Delta\rho_j(x'') \ge 0 \text{ for all } j < i, \qquad \rho_j(x) \ge 0 \text{ for all } j \le i, \qquad \Delta\rho_i(x'') > 0 .$$

Every [lexicographic-linear ranking function](lexicographic-linear-ranking-functions.md) is a weak LLRF; the definition replaces the required decrease $\Delta\rho_i(x'') \ge 1$ by strict positivity. Over the integers, a weak LLRF with integer coefficients is an LLRF, since a positive integer decrease is at least $1$, so the existence of a weak LLRF implies the existence of an LLRF; over the rationals the decreases need not be bounded away from $0$, so a weak LLRF need not be an LLRF (Example 5.25 of the source), though an LLRF can be [built from it](weak-llrfs-yield-llrfs-over-the-rationals.md).

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)
- [Lexicographic-linear ranking functions](lexicographic-linear-ranking-functions.md)

## Related topics

- [Weak LLRFs yield LLRFs over the rationals](weak-llrfs-yield-llrfs-over-the-rationals.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 5.3, Definition 5.24, the discussion after it and Example 5.25.
