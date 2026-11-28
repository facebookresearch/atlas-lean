# Hypergraph rewriting systems

A hypergraph rewriting system has a signature of node labels and typed hyperedge labels and a set of rules $L \supseteq K \to R$, applied to finite hypergraphs by double pushouts. It is finite if both label sets and the rule set are finite; termination and confluence refer to its derivation relation.

**Hypergraphs.** A signature $\mathcal{C} = \langle \mathcal{C}_V, \mathcal{C}_E \rangle$ consists of a set $\mathcal{C}_V$ of node labels and a set $\mathcal{C}_E$ of hyperedge labels, each $\ell \in \mathcal{C}_E$ having a type $\mathrm{type}(\ell) = \langle \alpha, \beta \rangle$ with $\alpha, \beta \in \mathcal{C}_V^*$. A hypergraph over $\mathcal{C}$ is $G = \langle V_G, E_G, l_G, m_G, s_G, t_G \rangle$ with finite sets $V_G$ of nodes and $E_G$ of hyperedges, labelings $l_G \colon V_G \to \mathcal{C}_V$ and $m_G \colon E_G \to \mathcal{C}_E$, and maps $s_G, t_G \colon E_G \to V_G^*$ assigning strings of source and target nodes such that $\mathrm{type}(m_G(e)) = \langle l_G^*(s_G(e)), l_G^*(t_G(e)) \rangle$. Morphisms preserve labels, sources and targets.

**Rules and derivations.** A rule $r = (L \supseteq K \xrightarrow{b} R)$ consists of hypergraphs $L$, $K$, $R$ with $K$ a subhypergraph of $L$ and a morphism $b \colon K \to R$ (not necessarily injective). For a morphism $g \colon L \to G$, $G$ directly derives $H$ through $r$ and $g$ if there are two hypergraph pushouts, one exhibiting $G$ as the gluing of $L$ and a context $D$ along $K$, the other exhibiting $H$ as the gluing of $R$ and $D$ along $K$. A hypergraph rewriting system $\mathcal{G} = \langle \mathcal{C}, \mathcal{R} \rangle$ is a signature with a set of rules; it is finite if $\mathcal{C}_V$, $\mathcal{C}_E$ and $\mathcal{R}$ are finite.

**Termination and confluence.** Write $\Rightarrow$ for the union of the direct derivations of $\mathcal{G}$ on finite hypergraphs over $\mathcal{C}$, taken up to isomorphism, and $\Rightarrow^*$ for its reflexive transitive closure. $\mathcal{G}$ is terminating if there is no infinite sequence $G_0 \Rightarrow G_1 \Rightarrow \cdots$, and confluent if whenever $H_1 \Leftarrow^* G \Rightarrow^* H_2$ there is $M$ with $H_1 \Rightarrow^* M \Leftarrow^* H_2$.

When all morphisms $b$ are inclusions and every hyperedge has one source and one target, this specializes to [double-pushout graph rewriting](double-pushout-graph-rewriting-systems.md), except that node labels are prescribed by the edge labels; to encode arbitrary labelled graphs, refine each edge label by the labels of its endpoints. For terminating hypergraph rewriting, joinability of all critical pairs does not imply local confluence, so the Knuth–Bendix critical pair test of term rewriting does not carry over; the same source proves a critical pair lemma under a stronger joinability condition.

## Depends on

- [Confluence of a relation](../../../../Logic/first-order-logic/term-rewriting/confluence-of-a-relation.md)

## Proof depends on

None.

## Sources

- Detlef Plump, "Hypergraph rewriting: critical pairs and undecidability of confluence", chapter 15 of M. R. Sleep, M. J. Plasmeijer and M. C. J. D. van Eekelen (eds.), *Term Graph Rewriting: Theory and Practice*, John Wiley & Sons, 201–213, 1993, read as the [accepted version](https://eprints.whiterose.ac.uk/id/eprint/243833/): Sections 15.2.1–15.2.2 (hypergraphs, rules and derivations) and Section 15.4 (finite systems).
