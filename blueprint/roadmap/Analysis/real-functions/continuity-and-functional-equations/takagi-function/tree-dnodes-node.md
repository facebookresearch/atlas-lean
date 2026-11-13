# Recursion for the number of $D$-nodes

Write $D(t)$ for the number of $D$-nodes of a
full binary tree $t$. If the root of $t$ has left subtree $l$ and right subtree $r$, then
$D(t) = \varepsilon + D(l) + D(r)$, where $\varepsilon = 0$ if $l$ and $r$ have the same number
of leaves and $\varepsilon = 1$ otherwise.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Definition (`S`-nodes and `D`-nodes).
