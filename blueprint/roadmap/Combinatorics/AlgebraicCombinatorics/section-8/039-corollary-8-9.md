---
article_id: af_b751e7935c7912ffc65b4f32
declaration: theorem
origin: cited
lean: PartitionCycles.partition_cycle_count
---

# Corollary 8.9

Fix $j \geq 1$. The number of ways to choose a partition $\lambda$ of $j$, then delete a square from $\lambda$ (keeping it a partition), then insert a square, then delete a square, etc., for a total of $m$ insertions and $m$ deletions, ending back at $\lambda$, is given by $$\sum_{s=1}^{j}[p(j-s) - p(j-s-1)]\, s^m, \quad m > 0.$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 8.8](038-theorem-8-8.md)

## Sources

- [MIT 18.318 Topics in Algebraic Combinatorics (Spring 2006), Section 8](../../../../sources/v1/AlgebraicCombinatorics.md)
