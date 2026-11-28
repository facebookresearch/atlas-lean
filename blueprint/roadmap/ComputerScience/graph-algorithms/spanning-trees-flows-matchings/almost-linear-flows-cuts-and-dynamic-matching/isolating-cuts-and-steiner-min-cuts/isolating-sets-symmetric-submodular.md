# Isolating sets for symmetric submodular functions and hypergraph cuts (Chekuri-Quanrud)

Let $f : 2^V \to \mathbb{R}$ be symmetric ($f(A) = f(V \setminus A)$) and submodular, and let $R \subseteq V$ with $|R| \ge 2$. Suppose an oracle returns, for any partition $(P, Q)$ of $R$, a set $A$ with $P \subseteq A \subseteq V \setminus Q$ minimizing $f(A)$. Then with $\lceil \log_2 |R| \rceil$ oracle calls one can compute sets $X_r$, $r \in R$, such that

1. $X_r \cap R = \{r\}$ for every $r \in R$,
2. $X_r \cap X_q = \emptyset$ for $r \ne q$, and
3. there is an $f$-minimum $(r, R \setminus \{r\})$-separating set $Y_r$ with $Y_r \subseteq X_r$.

In particular this applies to the cut function $f(A) = \sum_{e \in \delta(A)} w(e)$ of a hypergraph with nonnegative weights $w$, where $\delta(A)$ is the set of hyperedges meeting both $A$ and $V \setminus A$; nonnegativity makes $f$ submodular. Minimum isolating cuts in a hypergraph of total size $p = \sum_e |e|$ then reduce to $\lceil \log_2 |R| \rceil$ hypergraph minimum-cut computations on the whole hypergraph, each of total size $p$, followed by one minimum-cut computation for each $r \in R$ on the instance obtained by contracting the complement of its region, these instances having total size at most $2p$.

## Proof sketch

The bit-cut argument for graph cuts only uses symmetric submodularity of the cut function: for a minimal $f$-minimum isolating set $Y$ and a minimum separating set $X$ for coordinate $i$, submodularity and the feasibility of $Y \cup X$ show that $Y \cap X$ is again minimum, so $Y \subseteq X$. Intersecting over all coordinates gives disjoint regions $X_r$ containing the minimal minimizers. The hypergraph cut function is symmetric, and submodular because the weights are nonnegative. After contracting the complement of a region $U_r$ into one vertex, a hyperedge $e$ has size at most $|e \cap U_r| + 1$ in that instance and appears only in instances whose region it meets, so its total contribution is at most $2|e|$, which gives the $O(p)$ bound.

## Depends on

- [Submodular set function](../../../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [Minimal minimum isolating cuts lie in disjoint bit-cut regions](bit-cut-region-containment.md)

## Sources

- Chandra Chekuri, Kent Quanrud, "Isolating Cuts, (Bi-)Submodularity, and Faster Algorithms for Global Connectivity Problems", ICALP (2021), arXiv:2103.12908.
- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
