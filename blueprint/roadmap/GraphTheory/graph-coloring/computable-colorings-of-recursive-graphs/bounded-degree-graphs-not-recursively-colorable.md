# Highly recursive k-chromatic graphs of bounded degree need not be recursively k-colorable

For every $k \ge 2$ there is a highly recursive graph of maximum degree at most $2k - 2$ with chromatic number $k$ that has no recursive $k$-coloring; it is recursively $(k+1)$-colorable.

A graph $G = (V, E)$ with $V \subseteq \mathbb{N}$ is *recursive* if $V$ and $E$ are decidable sets, and *highly recursive* if moreover every vertex has finite degree and the function sending a vertex to (a code of) its finite set of neighbors is computable. A *$k$-coloring* is a map $c \colon V \to \{1, \dots, k\}$ with $c(u) \ne c(v)$ for every edge $uv$; $G$ is *recursively $k$-colorable* if some computable function is a $k$-coloring of $G$. The *chromatic number* $\chi(G)$ is the least $k$ for which a $k$-coloring exists, and the *recursive chromatic number* $\chi_r(G)$ the least $k$ for which $G$ is recursively $k$-colorable.

**Theorem (Bean; Manaster and Rosenstein).** For every integer $k \ge 2$ there is a highly recursive graph $G$ in which every vertex has degree at most $2k - 2$, with $\chi(G) = k$ and $\chi_r(G) = k + 1$. In particular every $k$-coloring of $G$ is noncomputable.

By a remark of Schmerl, such a graph can be made $(2k - 2)$-regular without changing $\chi$ or $\chi_r$. For general highly recursive graphs the gap is bounded: a highly recursive $k$-colorable graph is recursively $(2k-1)$-colorable, uniformly in an index, and this bound is attained; for merely recursive graphs there is no bound at all, since some recursive $2$-colorable graph is not recursively colorable with finitely many colors. These statements are from the same survey, with their own attributions there.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The graph is built by diagonalizing against an effective enumeration of the partial computable functions, so that none of them is a $k$-coloring of $G$, while $G$ stays $k$-colorable, its degrees stay at most $2k - 2$ and its neighbor function stays computable; the details are in Bean's paper, and Manaster and Rosenstein reach the same bound by a different construction. A good expansion links the definitions of recursive and highly recursive graphs and of the recursive chromatic number, and the construction of Bean (or the different one of Manaster and Rosenstein).

## Sources

- W. Gasarch, "A survey of recursive combinatorics", in *Handbook of Recursive Mathematics, Volume 2: Recursive Algebra, Analysis and Combinatorics*, Studies in Logic and the Foundations of Mathematics 139, Elsevier, 1998, pp. 1041–1176, doi:10.1016/S0049-237X(98)80049-9; read in the author's open-access copy at <https://www.cs.umd.edu/~gasarch/papers/rcombsur.pdf>: Section 5.7.3 (Regular graphs), which states the theorem and Schmerl's remark, Definitions 5.4–5.6 and the summary after Potential Analogue 5.9 in Section 5.1 for the comparison results, in the numbering of that copy.
- D. R. Bean, "Effective coloration", *The Journal of Symbolic Logic* 41(2):469–480, 1976, doi:10.2307/2272247 (not read here; cited by the survey above).
- A. B. Manaster and J. G. Rosenstein, "Effective matchmaking and $k$-chromatic graphs", *Proceedings of the American Mathematical Society* 39(2):371–378, 1973, doi:10.1090/S0002-9939-1973-0340082-2 (not read here; cited by the survey above).
