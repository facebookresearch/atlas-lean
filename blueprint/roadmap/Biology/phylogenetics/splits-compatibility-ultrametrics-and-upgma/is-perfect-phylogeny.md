# Perfect phylogeny for a binary character matrix

An [unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md) $T$ on $X$ is a perfect phylogeny for a binary matrix $M : X \times J \to \{0, 1\}$ if for every column $j$, the [split](char-split.md) of the character $M(\cdot, j)$ is empty, is all of $X$, or is an [edge split](edge-splits.md) of $T$: every nonconstant character changes state on exactly one edge, and a constant character changes on none.
