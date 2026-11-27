# Spill everywhere is NP-complete on chordal graphs

The decision version of the [spill everywhere problem](the-spill-everywhere-problem.md) without holes is NP-complete on chordal graphs, which include the interference graphs of strict SSA programs by [the dominance elimination order](dominance-order-gives-a-perfect-elimination-order.md), even if $w(v) = 1$ for every variable. Hardness for strict SSA programs themselves would also need the converse, that every chordal graph is the interference graph of a strict SSA program, which is not claimed here. It remains NP-complete in the incremental case, where the register pressure only has to drop from $\Omega$ to $\Omega - 1$, again with unit weights.

**Proof idea.** Membership in NP is clear. For the incremental case, a chordal graph is the intersection graph of subtrees of a tree, and an instance of exact cover by 3-sets is encoded by a tree whose leaves correspond to the elements and subtrees that correspond to the triples.

## Depends on

- [Dominance order gives a perfect elimination order](dominance-order-gives-a-perfect-elimination-order.md)
- [The spill everywhere problem](the-spill-everywhere-problem.md)

## Proof depends on

- [EXACT COVER BY 3-SETS is NP-complete](../../../TheoryOfComputation/np-completeness/set-systems-and-location/exact-cover-by-3-sets/exact-cover-by3-sets-np-complete.md)

## Expansion

This page becomes ready once this prerequisite is stated:

- a graph has a perfect elimination order, that is, it is [chordal](perfect-elimination-orders-and-chordal-graphs.md), if and only if it is the intersection graph of a family of subtrees of a tree (F. Gavril, "The intersection graphs of subtrees in trees are exactly the chordal graphs", *Journal of Combinatorial Theory, Series B* 16(1):47–56, 1974), a proof prerequisite.

## Sources

- F. Bouchez, A. Darte and F. Rastello, "On the complexity of spill everywhere under SSA form", *Proceedings of the 2007 ACM SIGPLAN/SIGBED Conference on Languages, Compilers, and Tools for Embedded Systems (LCTES 2007)*, ACM, 2007, pp. 103–112, doi:10.1145/1254766.1254782, author copy with the same theorem numbering arXiv:0710.3642v1 <https://arxiv.org/abs/0710.3642>, Section 3, Theorem 3 (NP-completeness on chordal graphs, from M. Yannakakis and F. Gavril, "The maximum k-colorable subgraph problem for chordal graphs", *Information Processing Letters* 24(2):133–137, 1987), and Theorem 6 (the incremental problem, by reduction from exact cover by 3-sets) with its proof.
