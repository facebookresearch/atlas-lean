# Correctness of support enumeration for bimatrix games

Let $M$ and $N$ be finite nonempty sets of pure strategies, with $m = \lvert M \rvert$ and $n = \lvert N \rvert$, and let $A, B$ be
$M \times N$ payoff matrices with rational entries, given explicitly. For nonempty $I \subseteq M$ and $J \subseteq N$, the support system
$S(I, J)$ has unknowns $x \in \mathbb{R}^M$, $y \in \mathbb{R}^N$ and $u, v \in \mathbb{R}$ and the linear constraints $x \ge 0$,
$\sum_i x_i = 1$, $x_i = 0$ for $i \notin I$, $y \ge 0$, $\sum_j y_j = 1$, $y_j = 0$ for $j \notin J$, $(Ay)_i = u$ for $i \in I$ and
$(Ay)_i \le u$ for $i \in M$, and $(B^{\mathsf T} x)_j = v$ for $j \in J$ and $(B^{\mathsf T} x)_j \le v$ for $j \in N$. Support enumeration
runs through the at most $(2^m - 1)(2^n - 1)$ pairs $(I, J)$ in a fixed order and asks an exact linear-feasibility oracle, which on a
feasible system with rational coefficients returns one of its solutions and otherwise reports infeasibility, about $S(I, J)$; it outputs
$(x, y)$ for the first feasible pair. Then:

1. every pair $(x, y)$ returned is a [Nash equilibrium](is-bimatrix-nash.md) of $(A, B)$ (soundness);
2. some system $S(I, J)$ is feasible, so the procedure halts with an output after at most $(2^m - 1)(2^n - 1)$ oracle calls, each on a
   system with $m + n + 2$ unknowns and $O(m + n)$ constraints whose coefficients are entries of $A$ and $B$ or $0, \pm 1$ (completeness).

Rationality is used only for the oracle model. For real payoff matrices the same systems characterize the equilibria: $(x, y)$ is a Nash
equilibrium of $(A, B)$ if and only if, for some $u$ and $v$, $(x, y, u, v)$ solves $S(\operatorname{supp} x, \operatorname{supp} y)$, by the
best-response condition; and a Nash equilibrium exists, so some $S(I, J)$ is feasible.

## Expansion

This node states a precise result relative to an exact linear-feasibility oracle. A good expansion adds a page for each item below and
links it under the dependency sections:

- Statement prerequisite: the oracle model, namely what a query is, what it returns, and how calls are counted.
- Proof prerequisite, for an oracle-free version: for a finite system of linear equations and inequalities with rational coefficients,
  deciding feasibility and, when it is feasible, computing a rational solution exactly, with a stated bound on its cost.
- Example: for matching pennies ($A = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$, $B = -A$) only $S(M, N)$ is feasible, and the
  procedure returns the unique equilibrium $x = y = (1/2, 1/2)$ after testing at most all $9$ support pairs.

## Depends on

- [Explicit encoding and size of finite games](../explicit-encoding-and-size-of-finite-games.md)
- [Nash equilibrium of a bimatrix game](is-bimatrix-nash.md)

## Proof depends on

- [Nash's theorem](../nash-s-theorem/exists-is-mixed-nash.md)
- [Best-response (support) condition](../best-response-condition.md)

## Sources

- R. Savani and B. von Stengel, *Hard-to-solve bimatrix games*, Econometrica 74 (2006) 397–429, Lemma 1 (best responses are characterized by their supports, for real payoffs) and §1 (support enumeration). <http://www.maths.lse.ac.uk/Personal/stengel/TEXTE/savanistengel.pdf>
