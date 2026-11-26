# Interference graphs

Let a program be given as a sequence or control-flow graph of instructions over temporaries, with the result of [live-variables analysis](../static-analysis/live-variables-analysis.md): the set of temporaries live on leaving each instruction. The temporaries live on entry to the program, such as incoming parameters, are treated as defined together by an entry instruction. Two temporaries *interfere* if they belong to a common live-out set, or if one of them is defined by an instruction at whose exit the other is live; in particular, temporaries live on entry to the program pairwise interfere. The *interference graph* is the undirected graph whose nodes are the temporaries and whose edges join interfering temporaries.

A *register assignment with $k$ registers* maps each temporary to one of $k$ interchangeable registers so that interfering temporaries get different registers; it is a proper coloring of the interference graph with $k$ colors. A program can be allocated to $k$ registers without spilling exactly when its interference graph is $k$-colorable. The *core register allocation problem* takes a program and a number $K$ of registers, $K$ being part of the input, and asks whether such an assignment with $K$ registers exists.

Machine registers that particular instructions read or write are represented by *precolored* nodes, which interfere with every temporary live across those instructions; then an assignment must extend the fixed colors of the precolored nodes, and the equivalence above is with colorings that extend them. Two temporaries related by a move instruction, and not interfering, are *move-related*; giving them the same register lets the move be deleted.

## Depends on

- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Sources

- A. C. Myers, *Register Allocation*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/regalloc/index.html>: sections "Interference Graphs" (interference through common live-out sets and definitions, the interference graph, and register allocation with $k$ registers as $k$-coloring), "Precolored nodes" and "Move Coalescing" (move-related nodes).
