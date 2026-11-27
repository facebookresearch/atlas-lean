# Spill everywhere is NP-complete on chordal graphs

The decision version of the [spill everywhere problem](the-spill-everywhere-problem.md) without holes is NP-complete on chordal graphs, the interference graphs of strict SSA programs, even if $w(v) = 1$ for every variable. It remains NP-complete in the incremental case, where the register pressure only has to drop from $\Omega$ to $\Omega - 1$, again with unit weights.

**Proof idea.** Membership in NP is clear. For the incremental case, a chordal graph is the intersection graph of subtrees of a tree, and an instance of exact cover by 3-sets is encoded by a tree whose leaves correspond to the elements and subtrees that correspond to the triples.

## Depends on

- [The spill everywhere problem](the-spill-everywhere-problem.md)

## Proof depends on

- [EXACT COVER BY 3-SETS is NP-complete](../../../TheoryOfComputation/np-completeness/set-systems-and-location/exact-cover-by-3-sets/exact-cover-by3-sets-np-complete.md)

## Sources

- F. Bouchez, A. Darte and F. Rastello, "On the complexity of spill everywhere under SSA form", *Proceedings of the 2007 ACM SIGPLAN/SIGBED Conference on Languages, Compilers, and Tools for Embedded Systems (LCTES 2007)*, ACM, 2007, pp. 103–112, doi:10.1145/1254766.1254782, author copy with the same theorem numbering arXiv:0710.3642v1 <https://arxiv.org/abs/0710.3642>, Section 3, Theorem 3 (NP-completeness on chordal graphs, from M. Yannakakis and F. Gavril, "The maximum k-colorable subgraph problem for chordal graphs", *Information Processing Letters* 24(2):133–137, 1987), and Theorem 6 (the incremental problem, by reduction from exact cover by 3-sets) with its proof.
