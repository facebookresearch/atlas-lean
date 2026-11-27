# Minimum isolating cuts are closed under intersection and union

Let $G$, $R$ and $v \in R$ be as in the definition of isolating cuts. If $S$ and $T$ are minimum $v$-isolating cuts, then $S \cap T$ and $S \cup T$ are minimum $v$-isolating cuts. Consequently there is a unique inclusion-wise minimal minimum $v$-isolating cut, denoted $S_v^{*}$, and $S_v^{*} \subseteq S$ for every minimum $v$-isolating cut $S$.

## Proof sketch

The cut function $f(X) = w(\partial X)$ of an undirected graph with nonnegative weights is submodular: $f(S \cap T) + f(S \cup T) \le f(S) + f(T)$, since every edge counted on the left is counted at least as often on the right. Both $S \cap T$ and $S \cup T$ meet $R$ exactly in $\{v\}$, so each has value at least the minimum $\mu$, while the right-hand side equals $2\mu$; hence both equal $\mu$. Taking the intersection of all minimum $v$-isolating cuts yields the unique minimal one.

## Depends on

- [Minimum isolating cuts of a terminal set](minimum-isolating-cuts.md)
- [Submodular set function](../../../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Chandra Chekuri, Kent Quanrud, "Isolating Cuts, (Bi-)Submodularity, and Faster Algorithms for Connectivity", ICALP (2021), arXiv:2103.12908.
