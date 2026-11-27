# Total substitution cost of a labeling

For a [tree](../felsenstein-s-pruning-algorithm/tree.md) whose edges carry costs $c(a, b) \in \mathbb{N} \cup \{\infty\}$, a root state $s$ and a [labeling](../felsenstein-s-pruning-algorithm/labeling.md) $z$, the total cost is defined recursively: $0$ for a leaf, and for an internal node with edge costs $P, Q$ and children $l, r$ labeled $a, b$,

$$C(t, s, z) = P(s, a) + C(l, a, z_l) + Q(s, b) + C(r, b, z_r):$$

the sum over all edges of the cost from the parent's state to the child's state.
