# Dominators and loops

Computing the [dominance relation](../dominance-and-static-single-assignment-form.md) of a control-flow graph, and the loops it reveals. Dominator sets are the greatest solution of a distributive dataflow system, which the iterative algorithm of Cooper, Harvey and Kennedy solves with a dominator-tree representation; the algorithm of Lengauer and Tarjan computes immediate dominators from semidominators in almost linear time. Back edges, whose targets dominate their sources, define natural loops, the units of loop optimizations such as loop-invariant code motion.

- [Dominator sets as a dataflow problem](dominator-sets-as-a-dataflow-problem.md)
- [The Cooper–Harvey–Kennedy dominance algorithm](the-cooper-harvey-kennedy-dominance-algorithm.md)
- [Semidominators](semidominators.md)
- [Immediate dominators from semidominators](immediate-dominators-from-semidominators.md)
- [Computing semidominators from edges and ancestors](computing-semidominators.md)
- [Running time of the Lengauer–Tarjan algorithm](running-time-of-the-lengauer-tarjan-algorithm.md)
- [Back edges and natural loops](back-edges-and-natural-loops.md)
- [Natural loops are disjoint, nested or share a header](natural-loops-are-disjoint-nested-or-share-a-header.md)
- [Hoisting a loop-invariant assignment](hoisting-a-loop-invariant-assignment.md)
