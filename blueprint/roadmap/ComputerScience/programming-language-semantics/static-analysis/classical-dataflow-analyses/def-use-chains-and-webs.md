# Def-use chains and webs

Fix a variable $x$ of a program in control-flow-graph form, together with the solution of [reaching definitions analysis](reaching-definitions-analysis.md). The *DU-graph* of $x$ is the undirected graph with a node for each definition of $x$ and a node for each use of $x$, where a node of the control-flow graph that both uses and defines $x$ contributes two distinct nodes, and with an edge between a definition $d$ and a use $u$ whenever $d$ reaches the node containing $u$.

- A *DU-chain* is the subgraph connecting one definition to all the uses it reaches.
- A *UD-chain* is the subgraph connecting one use to all the definitions that reach it.
- A *web* of $x$ is a connected component of its DU-graph. Equivalently, it is a maximal set of DU-chains and UD-chains closed under intersection: two chains that share a node belong to the same web.

Different webs of one variable never communicate values: no definition of one web reaches a use of another, so each web can be renamed to a fresh variable, and hence allocated a register, without changing the behavior of the program. The webs of all variables can be computed from the def-use edges with a union-find structure, in time nearly linear in the number of def-use edges.

## Depends on

- [Reaching definitions analysis](reaching-definitions-analysis.md)

## Sources

- A. C. Myers, *Reaching definitions and SSA*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/reachdef/index.html>: section "Webs" (the DU-graph, DU-chains and UD-chains, webs as connected components and as maximal intersecting sets of chains, webs as the unit of register allocation, and their computation by union-find with path compression in nearly linear time).
- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 5.7 (the def-use graph built from reaching definitions).
