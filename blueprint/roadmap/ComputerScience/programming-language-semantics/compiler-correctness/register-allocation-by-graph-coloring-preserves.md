# Register allocation by graph coloring preserves semantics

For a program in a control-flow-graph representation in which no instruction reads or clobbers fixed hardware registers and all variables belong to one register class, let the interference graph be built by Chaitin's interference rules from the solution of live-variables analysis, with the program variables as vertices. If $c$ is a proper coloring of the interference graph with $k$ colors, then renaming every variable $x$ to the register $c(x)$ preserves the observable behavior of the program.

## Depends on

- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Proof depends on

- [Simulation diagrams for compiler correctness](simulation-diagrams-for-compiler-correctness.md)

## Sources

- X. Leroy, "Formal verification of a realistic compiler", *Communications of the ACM* 52(7):107–115, 2009, Sections 4.2 and 4.3
- Original method: G. J. Chaitin, "Register allocation and spilling via graph coloring", *SIGPLAN Symposium on Compiler Construction*, 1982. Leroy's compiler overview performs register allocation by coloring an interference graph and credits the method to it.
