# Register allocation is NP-complete

**Theorem (Chaitin et al.).** The [core register allocation problem](interference-graphs.md), with the number $K$ of registers part of the input, is NP-complete.

It is in NP because a register assignment is a certificate whose validity is checked against the interference graph in polynomial time. Hardness is by reduction from [graph coloring](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-coloring/graph-coloring-np-complete.md): from a finite undirected graph $G$ and a number $k$ one builds, in polynomial time, a program $P$ and a register count $K$ such that $P$ can be allocated to $K$ registers exactly when $G$ is $k$-colorable. The constructions in the literature add auxiliary temporaries, so the interference graph is not literally the input graph.

## Depends on

- [Interference graphs](interference-graphs.md)

## Proof depends on

- [GRAPH COLORING is NP-complete](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-coloring/graph-coloring-np-complete.md)

## Sources

- F. M. Q. Pereira and J. Palsberg, "Register allocation after classical SSA elimination is NP-complete", *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, <https://web.cs.ucla.edu/~palsberg/paper/fossacs06.pdf>, Section 1.1: the definition of the core register allocation problem, with $K$ part of the input, and the statement that Chaitin et al. showed it NP-complete by a reduction from graph coloring whose essence is that every graph is the interference graph of some program.
- A. C. Myers, *Register Allocation*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/regalloc/index.html>: section "Interference Graphs" (register allocation with $k$ registers as $k$-coloring of the interference graph, credited to Chaitin et al.).

## Expansion

This page needs a source check before it is ready: the original paper of Chaitin et al. ("Register allocation via coloring", *Computer Languages*, 1981), which contains the reduction, has to be read to state its program construction and its exact assumptions.
