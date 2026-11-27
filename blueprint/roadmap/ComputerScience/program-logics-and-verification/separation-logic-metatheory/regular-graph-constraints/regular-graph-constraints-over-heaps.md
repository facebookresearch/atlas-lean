# Regular graph constraints over heaps

A regular graph constraint is a finite graph $G'$; a graph satisfies it when it maps homomorphically into $G'$ preserving the root and null nodes, so $G'$ is a summary of the heap shapes it allows.

**Graphs and heaps.** A *graph* is a structure $G = \langle V, s_1, s_2, \mathrm{null}, \mathrm{root} \rangle$ with a finite set $V$ of nodes, distinct constants $\mathrm{root}, \mathrm{null} \in V$ and two edge relations $s_1, s_2 \subseteq V \times V$ (two pointer fields) such that, for $i \in \{1, 2\}$, $\langle \mathrm{null}, x \rangle \in s_i$ iff $x = \mathrm{null}$. A *heap* is a graph in which $s_1$ and $s_2$ are total functions and every node other than $\mathrm{null}$ is reachable from $\mathrm{root}$.

**Homomorphisms.** A map $h \colon V \to V'$ is a homomorphism from $G$ to $G' = \langle V', s'_1, s'_2, \mathrm{null}', \mathrm{root}' \rangle$ if every $\langle x, y \rangle \in s_i$ satisfies $\langle h(x), h(y) \rangle \in s'_i$ for $i \in \{1, 2\}$, $h(x) = \mathrm{root}'$ iff $x = \mathrm{root}$, and $h(x) = \mathrm{null}'$ iff $x = \mathrm{null}$. Write $G \to G'$ if a homomorphism exists; then $G$ *satisfies the constraint* $G'$.

**Decision problems.** For a class $\mathcal C$ of graphs, $G'$ is *satisfiable over* $\mathcal C$ if $H \to G'$ for some $H \in \mathcal C$, and $G_1$ *implies* $G_2$ *over* $\mathcal C$ if every $H \in \mathcal C$ with $H \to G_1$ satisfies $H \to G_2$. The implication problem over $\mathcal C$ asks, given finite graphs $G_1$ and $G_2$, whether $G_1$ implies $G_2$ over $\mathcal C$.

## Depends on

None.

## Proof depends on

None.

## Expansion

A homomorphism is a coloring: the color $h(x)$ of a node restricts the colors of its $s_1$- and $s_2$-successors. For instance a graph is $k$-colorable iff it maps to the complete loop-free graph on $k$ colors. Regular graph constraints are strictly less expressive than existential monadic second-order logic over graphs. Satisfiability over heaps is decidable, and implication over the class of all graphs is decidable because $G_1$ implies $G_2$ over all graphs iff $G_1 \to G_2$.

## Sources

- Viktor Kuncak and Martin Rinard, "Existential Heap Abstraction Entailment Is Undecidable", in *Static Analysis (SAS 2003)*, Lecture Notes in Computer Science 2694, Springer, 2003, pp. 418–438, <https://doi.org/10.1007/3-540-44898-5_24>; read as the technical report arXiv:cs/0408014v1, "Typestate Checking and Regular Graph Constraints", <https://arxiv.org/abs/cs/0408014v1>: Section 2 ("Regular Graph Constraints"), the definitions of graphs, heaps, homomorphisms, satisfiability and implication, and the decidability results in the same section of that version.
