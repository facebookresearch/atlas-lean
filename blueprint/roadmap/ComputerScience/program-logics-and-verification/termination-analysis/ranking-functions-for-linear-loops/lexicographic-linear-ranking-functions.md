# Lexicographic-linear ranking functions

A $d$-dimensional affine function $\tau = \langle \rho_1, \dots, \rho_d \rangle$ on $\mathbb{Q}^n$ is a *lexicographic-linear ranking function* (LLRF) for a set $T \subseteq \mathbb{Q}^{2n}$ of transitions if for every $x'' = (x, x') \in T$ there is an index $i \le d$ such that

- $\rho_j(x) - \rho_j(x') \ge 0$ for all $j < i$,
- $\rho_j(x) \ge 0$ for all $j \le i$, and
- $\rho_i(x) - \rho_i(x') \ge 1$;

$x''$ is then *ranked* by $\rho_i$. It is an LLRF for a rational, respectively integer, [linear-constraint loop](linear-constraint-loops.md) with transition polyhedra $Q_1, \dots, Q_k$ if it is an LLRF for $\bigcup_i Q_i$, respectively $\bigcup_i I(Q_i)$. An LLRF implies termination: along any run $\rho_1$ never increases, and each step ranked by $\rho_1$ needs $\rho_1 \ge 0$ and lowers it by at least $1$, so only finitely many steps are ranked by $\rho_1$; after the last of them $\rho_2$ never increases, and so on by induction on the components. The decision problems $\mathrm{LexLinRF}(\mathbb{Q})$ and $\mathrm{LexLinRF}(\mathbb{Z})$ ask whether a multipath loop has an LLRF as a rational, respectively integer, loop. This class is more permissive than earlier lexicographic notions that require every component to be nonnegative on every transition.

## Depends on

- [Linear ranking functions](linear-ranking-functions.md)
- [Linear-constraint loops](linear-constraint-loops.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 2.4, Definitions 2.11 and 2.14, Example 2.12.
