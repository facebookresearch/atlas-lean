# Register allocation by graph coloring preserves semantics

For a program in a control-flow-graph representation, let the interference graph have the program variables as vertices and an edge between two variables when one is defined at a point where the other is live (and they are not related by a move). If $c$ is a proper coloring of the interference graph with $k$ colors, then renaming every variable $x$ to the register $c(x)$ preserves the observable behavior of the program.

## Depends on

- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Proof depends on

- [Simulation diagrams for compiler correctness](simulation-diagrams-for-compiler-correctness.md)

## Sources

- X. Leroy, "Formal verification of a realistic compiler", *Communications of the ACM* 52(7):107–115, 2009
- Original method: G. J. Chaitin, "Register allocation and spilling via graph coloring", *SIGPLAN Symposium on Compiler Construction*, 1982. Leroy's compiler overview performs register allocation by coloring an interference graph and credits the method to it.
