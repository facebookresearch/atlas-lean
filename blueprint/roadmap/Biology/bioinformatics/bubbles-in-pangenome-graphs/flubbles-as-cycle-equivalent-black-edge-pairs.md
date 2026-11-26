# Flubbles: variant bubbles as cycle-equivalent edge pairs in variation graphs

**Setting.** A *biedged graph* $G = (V, E)$ has two kinds of edges: every vertex is incident with at most one *black* edge, black edges join the two sides $(x, \mathrm{tail})$ and $(x, \mathrm{head})$ of a sequence segment $x$ (and carry its label), and *grey* edges encode adjacencies between segment sides. It is equivalent to a bidirected sequence graph, so that both DNA strands can be traversed; a *variation graph* is a biedged sequence graph, assumed connected and *compact* (no linear chain contains more than one black edge). Two edges $a, b$ are **cycle equivalent** when every cycle through $a$ also passes through $b$ and vice versa.

Root a depth-first spanning tree $T_s$ of $G$ at a vertex $s$ (a dummy root joined to all tips, if $G$ has tips). Every non-tree edge joins a vertex to one of its ancestors in $T_s$ (a *back-edge*); a *bracket* of a tree edge $e$ is a back-edge joining a descendant of $e$ to an ancestor of $e$; and two tree edges are cycle equivalent in the augmented tree $T'_s$ iff they have the same bracket set.

**Definition.** A **flubble** is a pair $\langle e_1, e_2 \rangle$ of distinct black edges of $T_s$ that open and close one cycle-equivalence class of $T'_s$. Then $e_1, e_2$ lie on a common root–leaf path, several walks connect them, and removing both disconnects $G$, so the pair cuts out the subgraph whose traversals spell the alternative alleles of a variant between a common left and right context.

**Theorem.** A biedged graph $G = (V, E)$ has at most $|E|$ flubbles, and the **flubble tree**, which records all flubbles together with their nesting, can be computed in time linear in the size of $G$.

**Hairpins.** A *hairpin* is a subgraph that one black edge disconnects from the rest of $G$ and that contains a cycle with the same property: a loop reached through a stem that must be traversed both ways, so it represents an inversion. If $G$ contains a hairpin, at least one edge of $T_s$ has no bracket in $T'_s$, so hairpins are found in the same linear-time pass.

## Expansion

The number of back-edges of a DFS tree is less than the number of tree edges, and each cycle-equivalence class, hence each flubble, is opened by a change in the bracket set, so there are at most about as many flubbles as back-edges, giving the $|E|$ bound. Cycle-equivalence classes of tree edges are computed in one reverse-DFS sweep with compact bracket-list representations, as in the classical linear-time construction of the program structure tree of a control-flow graph. Because classes are properly nested along root–leaf paths, the opening and closing edges of each class produce a laminar family that is exactly the flubble tree. Flubbles generalize superbubbles (defined for directed graphs) and ultrabubbles/snarls (2-black-edge-connected subgraphs of biedged graphs) while keeping the linear count that makes enumeration efficient.

## Sources

- N. Mwaniki, E. Garrison and N. Pisanti, *Popping bubbles in pangenome graphs*, arXiv:2410.20932 (2024), Section 2 (biedged graphs, cycle-equivalent edge pairs), Section 3 (bubbles, superbubbles, snarls) and Section 4 (Observation 1, Section 4.2 theorem and corollary on the flubble tree). <https://doi.org/10.48550/arXiv.2410.20932>
