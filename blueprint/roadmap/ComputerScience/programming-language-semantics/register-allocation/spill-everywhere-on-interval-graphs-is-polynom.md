# Spill everywhere on interval graphs is polynomial

For the [spill everywhere problem](the-spill-everywhere-problem.md) without holes on an interval graph, the interference graph of a basic block:

1. if $w(v) = 1$ for all $v$, a greedy algorithm that, at each point where the pressure exceeds $r$, spills the live variable whose interval ends furthest away solves the problem in polynomial time, for any $r$;
2. with arbitrary weights it is solvable in polynomial time for any $r$, as an integer linear program whose constraint matrix, with one row per point and one column per interval, has the consecutive-ones property and is therefore totally unimodular.

## Depends on

- [The spill everywhere problem](the-spill-everywhere-problem.md)

## Sources

- F. Bouchez, A. Darte and F. Rastello, "On the complexity of spill everywhere under SSA form", research report RR2007-42, LIP, ENS Lyon, arXiv:0710.3642v1, <https://arxiv.org/abs/0710.3642> (also *LCTES 2007*), Section 3: Theorem 1 (furthest first, after Belady's furthest-use strategy) and Theorem 2 (the totally unimodular formulation, pointed out by Gavril and Yannakakis) with their proofs.
