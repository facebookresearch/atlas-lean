# Fitch's algorithm

For observed states $\sigma$ and a [tree](../felsenstein-s-pruning-algorithm/tree.md) (its edge weights are ignored), Fitch's algorithm returns a set of states and a count: $(\{\sigma(l)\}, 0)$ for a leaf $l$; for an internal node whose children return $(A, m)$ and $(B, n)$, it returns $(A \cap B, m + n)$ if $A \cap B \ne \emptyset$ and $(A \cup B, m + n + 1)$ otherwise.
