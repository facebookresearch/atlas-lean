# Lexicographic-linear ranking functions

A $d$-dimensional affine function $\tau = \langle \rho_1, \dots, \rho_d \rangle$ on $\mathbb{Q}^n$ is a *lexicographic-linear ranking function* (LLRF) for a set $T \subseteq \mathbb{Q}^{2n}$ of transitions if for every $x'' = (x, x') \in T$ there is an index $i \le d$ such that

- $\rho_j(x) - \rho_j(x') \ge 0$ for all $j < i$,
- $\rho_j(x) \ge 0$ for all $j \le i$, and
- $\rho_i(x) - \rho_i(x') \ge 1$;

$x''$ is then *ranked* by $\rho_i$. It is an LLRF for a rational, respectively integer, [linear-constraint loop](linear-constraint-loops.md) with transition polyhedra $Q_1, \dots, Q_k$ if it is an LLRF for $\bigcup_i Q_i$, respectively $\bigcup_i I(Q_i)$. An LLRF implies termination, since $x \mapsto \langle \max(0, \rho_1(x)), \dots, \max(0, \rho_d(x)) \rangle$ decreases at every transition in the lexicographic extension of the well-founded order $a \prec b \iff a + 1 \le b$ on $\mathbb{Q}_{\ge 0}$. The decision problems $\mathrm{LexLinRF}(\mathbb{Q})$ and $\mathrm{LexLinRF}(\mathbb{Z})$ ask whether a multipath loop has an LLRF as a rational, respectively integer, loop. This class is more permissive than earlier lexicographic notions that require every component to be nonnegative on every transition.

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", arXiv:1208.4041v4, 2025, <https://arxiv.org/abs/1208.4041v4>, Section 2.4, Definitions 2.11 and 2.14, Example 2.12.
