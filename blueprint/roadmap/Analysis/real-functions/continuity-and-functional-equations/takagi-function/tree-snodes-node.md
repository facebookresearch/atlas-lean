# Recursion for the number of $S$-nodes

Write $S(t)$ for the number of $S$-nodes of a
full binary tree $t$. If the root of $t$ has left subtree $l$ and right subtree $r$, then
$S(t) = \varepsilon + S(l) + S(r)$, where $\varepsilon = 1$ if $l$ and $r$ have the same number
of leaves and $\varepsilon = 0$ otherwise.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes).
