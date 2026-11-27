# Adaptive tests reading at most t blocks cannot distinguish t-wise independent blocks

Let $G$ map a uniform seed to blocks $(G_x)_{x \in X}$, each block a string in $\{0,1\}^\kappa$, such that the blocks form a $t$-wise independent family. Let a test first sample independent random coins to select a decision tree, then adaptively read bits of the blocks, touching bits from at most $t$ distinct blocks on every input (reading whole blocks is allowed). Then the output distribution of the test on $G$ equals its output distribution on independent uniform blocks.

## Proof sketch

Apply the subcube transfer with $d$ the difference between $G$'s law and the uniform law: every subcube determined by bits of at most $t$ blocks has the same probability under both, so $\varepsilon = 0$; average over the test's coins.

## Depends on

- [k-wise independent hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)
- [Subcube bounds transfer to adaptive decision-tree tests](subcube-bounds-transfer-to-decision-trees.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
