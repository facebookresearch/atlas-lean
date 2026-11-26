# Spill everywhere with few registers on chordal graphs

For every fixed number $r$ of registers, the [spill everywhere problem](the-spill-everywhere-problem.md) without holes is solvable in polynomial time on chordal graphs, even with arbitrary weights.

**Proof idea.** Represent the chordal graph as the intersection graph of subtrees of a tree and compute, by dynamic programming bottom up over the points of the tree, for each set of at most $r$ variables kept in registers at a point, the maximum weight of the variables that can be kept in the subtree below it. There are polynomially many such sets for fixed $r$.

## Depends on

- [The spill everywhere problem](the-spill-everywhere-problem.md)

## Sources

- F. Bouchez, A. Darte and F. Rastello, "On the complexity of spill everywhere under SSA form", *Proceedings of the 2007 ACM SIGPLAN/SIGBED Conference on Languages, Compilers, and Tools for Embedded Systems (LCTES 2007)*, ACM, 2007, pp. 103–112, doi:10.1145/1254766.1254782, author copy with the same theorem numbering arXiv:0710.3642v1 <https://arxiv.org/abs/0710.3642>, Section 3, Theorem 4 (dynamic programming on non-spilled variables) with its proof, and the remark that M. Yannakakis and F. Gavril (1987) proved the same result.
