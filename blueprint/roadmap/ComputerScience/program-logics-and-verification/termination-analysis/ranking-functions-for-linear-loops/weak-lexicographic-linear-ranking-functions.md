# Weak lexicographic-linear ranking functions

Let $Q_1, \dots, Q_k$ be the transition polyhedra of a multipath [linear-constraint loop](linear-constraint-loops.md), and for an affine $\rho$ write $\Delta\rho(x'') = \rho(x) - \rho(x')$ for a transition $x'' = (x, x')$. A $d$-tuple $\tau = \langle \rho_1, \dots, \rho_d \rangle$ of affine functions is a *weak lexicographic-linear ranking function* (weak LLRF) for $Q_1 \cup \dots \cup Q_k$ if every transition $x''$ in the union has an index $i \le d$ with

$$\Delta\rho_j(x'') \ge 0 \text{ for all } j < i, \qquad \rho_i(x) \ge 0, \qquad \Delta\rho_i(x'') > 0 .$$

Every [lexicographic-linear ranking function](lexicographic-linear-ranking-functions.md) is a weak LLRF; the definition replaces the required decrease $\Delta\rho_i(x'') \ge 1$ by strict positivity. Over the integers a weak LLRF is already an LLRF; over the rationals a weak LLRF need not even imply termination by itself, since positive rationals can decrease forever.

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)
- [Lexicographic-linear ranking functions](lexicographic-linear-ranking-functions.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", arXiv:1208.4041v4, 2025, <https://arxiv.org/abs/1208.4041v4>, Section 5.3, Definition 5.24 and the discussion after it.
