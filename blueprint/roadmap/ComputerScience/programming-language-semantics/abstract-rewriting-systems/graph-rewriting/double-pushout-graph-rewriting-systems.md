# Double-pushout graph rewriting systems

A graph rewriting system is a finite label alphabet with a finite set of rules $L \supseteq K \subseteq R$; a rule applies to a finite graph through a label-preserving morphism of $L$ that satisfies the dangling and identification conditions, deleting $L - K$ and adding $R - K$. Termination asks for the absence of infinite derivations.

**Graphs.** A label alphabet $\mathcal{C} = \langle \mathcal{C}_V, \mathcal{C}_E \rangle$ is a pair of finite sets of vertex labels and edge labels. A graph over $\mathcal{C}$ is a system $G = \langle V_G, E_G, s_G, t_G, l_G, m_G \rangle$ of two finite sets $V_G$ (vertices) and $E_G$ (edges), source and target functions $s_G, t_G \colon E_G \to V_G$, and labeling functions $l_G \colon V_G \to \mathcal{C}_V$ and $m_G \colon E_G \to \mathcal{C}_E$. Parallel edges and loops are allowed. A graph morphism $f \colon G \to H$ is a pair of maps $f_V \colon V_G \to V_H$, $f_E \colon E_G \to E_H$ preserving sources, targets and labels; $H$ is a subgraph of $G$ when both vertex and edge sets are subsets and the four functions are restrictions.

**Rules and derivations.** A rule $r = (L \supseteq K \subseteq R)$ consists of graphs $L$, $K$, $R$ over $\mathcal{C}$ with the interface $K$ a subgraph of both the left-hand side $L$ and the right-hand side $R$. A morphism $f \colon L \to G$ satisfies the gluing condition if

- (dangling) no edge of $G - f(L)$ is incident to a vertex of $f(L) - f(K)$, and
- (identification) for distinct items $x, y$ of $L$ (vertices or edges, separately), $f(x) = f(y)$ only if $x, y \in K$.

Then $G$ directly derives $H$ by $r$, written $G \Rightarrow_r H$, if $H$ is isomorphic to the graph obtained by removing the items of $f(L) - f(K)$ from $G$, giving a subgraph $D$, and adding disjointly the items of $R - K$, an added edge whose source (target) lies in $K$ being attached to the image of that vertex under $f$; equivalently, $H$ is the result of a double pushout of graph morphisms. A graph rewriting system $\mathcal{G} = \langle \mathcal{C}, \mathcal{R} \rangle$ consists of a label alphabet and a finite set $\mathcal{R}$ of rules over it; $G \Rightarrow_{\mathcal{R}} H$ if $G \Rightarrow_r H$ for some $r \in \mathcal{R}$.

**Termination and cyclicity.** $\mathcal{G}$ is terminating if there is no infinite sequence $G_0 \Rightarrow_{\mathcal{R}} G_1 \Rightarrow_{\mathcal{R}} \cdots$ of finite graphs over $\mathcal{C}$, starting from any graph. $\mathcal{G}$ is cyclic if it admits a derivation in which some graph occurs twice (up to isomorphism); a cyclic system is non-terminating, but not conversely.

This is the double-pushout ("Berlin") approach of Ehrig and coauthors, with injective inclusions $K \subseteq L$ and $K \subseteq R$. Unlike term or string rewriting, graph rewriting acts on arbitrary graphs, including cyclic ones: the single rule that rewrites a path labeled $ab$ into a path labeled $ba$ terminates on string graphs but not on a cycle labeled $a, b$, which is why termination of string rewriting does not transfer directly.

## Depends on

- [Abstract reduction system](../../../../Logic/first-order-logic/term-rewriting/abstract-reduction-system.md)

## Proof depends on

None.

## Sources

- Detlef Plump, "Termination of graph rewriting is undecidable", *Fundamenta Informaticae* 33(2), 201–209, 1998, <https://doi.org/10.3233/FI-1998-33204>; read as the accepted version, <https://eprints.whiterose.ac.uk/id/eprint/243324/>, which carries the journal's numbering: Section 2 (graph rewriting and termination), Section 4 before Theorem 4.1 (cyclicity) and Section 1 (the $ab \to ba$ example).
