# Shortest paths and cluster properties of ranked SPR

Let $d_{\mathrm{HSPR}}$ and $d_{\mathrm{RSPR}}$ be the horizontal and ranked SPR distances on ranked trees with $n$ leaves. A treespace has the **weak cluster property** if, whenever two trees share a cluster, some shortest path between them keeps that cluster in every tree along it.

**Theorem 7.** HSPR and RSPR do not have the weak cluster property. For example, $T = [\{l_1, l_2\}, \{l_1, l_2, l_3\}, \{l_4, l_5\}]$ and $R = [\{l_4, l_5\}, \{l_2, l_3\}, \{l_1, l_4, l_5\}]$ share $\{l_4, l_5\}$, but no shortest path between them preserves it.

**Theorem 8.** Between any two trees there is a shortest HSPR path along which the ranks of the HSPR moves increase monotonically.

**Theorem 9.** If $T$ and $R$ both have the cherry $\{x, y\}$ at rank one, then every tree on every shortest HSPR path between them has $\{x, y\}$ as its cherry at rank one; consequently (Corollary 3) deleting $x$ from both trees does not change their HSPR distance.

**Theorem 10.** In RSPR, some shortest path between any two trees performs all its rank moves first and only HSPR moves afterwards (and symmetrically, HSPR moves first and rank moves last).

**Theorem 11.** Adding one leaf to two trees can decrease their HSPR distance by $\lceil (n-1)/2 \rceil - 1$.

**Theorem 12.** If $d_{\mathrm{HSPR}}(T, R) = d > 1$ and adding a leaf $x$ to both yields trees at HSPR distance $1$, then the unranked versions satisfy $d_{\mathrm{SPR}}(T^u, R^u) = 1$.

## Depends on

- [Horizontal and ranked SPR treespaces](horizontal-and-ranked-spr-treespaces.md)

## Expansion

In the counterexample of Theorem 7, the cluster $\{l_4, l_5\}$ sits at rank $3$ in $T$ and rank $1$ in $R$; HSPR moves never change ranks, and the only cluster-preserving moves from $T$ cannot lower that node, so every path that keeps the cluster is longer than the distance. Monotone ordering (Theorem 8) comes from a commutation lemma: two consecutive HSPR moves at ranks $k > i$ can be replaced by a move at rank $i$ followed by one at rank $k$. Theorems 11 and 12 contrast with unranked SPR, where deleting a common leaf never increases distance by much; in ranked space a new leaf placed at rank one can shortcut many rank-constrained moves, a sign that ranked SPR distances behave differently from their unranked counterparts and from ranked NNI, which does have the cluster property and polynomial-time distances.

## Sources

- L. Collienne, C. Whidden, A. Gavryushkin, "Ranked subtree prune and regraft", Bulletin of Mathematical Biology 86 (2024) 24, Theorems 7–12, Corollary 3, <https://doi.org/10.1007/s11538-023-01244-2> (PMC10830682).
