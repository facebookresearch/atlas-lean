# Register allocation is NP-complete

The *core register allocation problem* takes as input a program $P$ and a number $K$ of registers, $K$ being part of the input, and asks whether each temporary of $P$ can be mapped to one of $K$ registers so that temporaries with [interfering](interference-graphs.md) live ranges get different registers.

**Theorem (Chaitin et al.).** The core register allocation problem is NP-complete. The proof reduces graph coloring to it: every finite undirected graph is the interference graph of some program, which can be built from the graph in polynomial time.

The problem is in NP because a register assignment is a certificate whose validity is checked against the interference graph in polynomial time.

## Depends on

- [Interference graphs](interference-graphs.md)

## Sources

- F. M. Q. Pereira and J. Palsberg, "Register allocation after classical SSA elimination is NP-complete", *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, <https://web.cs.ucla.edu/~palsberg/paper/fossacs06.pdf>, Section 1.1: the definition of the core register allocation problem, with $K$ part of the input, and the statement that Chaitin et al. showed it NP-complete by a reduction from graph coloring whose essence is that every graph is the interference graph of some program.
- A. C. Myers, *Register Allocation*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/regalloc/index.html>: section "Interference Graphs" (register allocation with $k$ registers as $k$-coloring of the interference graph, credited to Chaitin et al.).

## Expansion

This page needs a source check before it is ready: the original paper of Chaitin et al. ("Register allocation via coloring", *Computer Languages*, 1981), which contains the reduction, has to be read to state its program construction and its exact assumptions.
