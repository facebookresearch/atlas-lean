# Spill everywhere is NP-complete on chordal graphs

The decision version of the [spill everywhere problem](the-spill-everywhere-problem.md) without holes is NP-complete on chordal graphs, the interference graphs of strict SSA programs, even if $w(v) = 1$ for every variable. It remains NP-complete in the incremental case, where the register pressure only has to drop from $\Omega$ to $\Omega - 1$, again with unit weights.

**Proof idea.** Membership in NP is clear. For the incremental case, a chordal graph is the intersection graph of subtrees of a tree, and an instance of exact cover by 3-sets is encoded by a tree whose leaves correspond to the elements and subtrees that correspond to the triples.

## Depends on

- [The spill everywhere problem](the-spill-everywhere-problem.md)

## Sources

- F. Bouchez, A. Darte and F. Rastello, "On the complexity of spill everywhere under SSA form", *LCTES 2007*, ACM, 2007; research report RR2007-42, LIP, ENS Lyon, <https://arxiv.org/abs/0710.3642>, Section 3.1, Theorem 3 (NP-completeness on chordal graphs, from M. Yannakakis and F. Gavril, "The maximum k-colorable subgraph problem for chordal graphs", *Information Processing Letters* 24(2):133–137, 1987), and Section 3.2, Theorem 6 (the incremental problem, by reduction from exact cover by 3-sets) with its proof.
