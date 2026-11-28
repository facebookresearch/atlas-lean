# The universal theory of hyperbolic groups is undecidable

The universal theory of the class of all hyperbolic groups is undecidable, and some lacunary hyperbolic group has exactly this universal theory, so its own universal theory is undecidable.

A universal sentence in the first-order language of groups is a sentence $\forall x_1 \dots \forall x_k\, \Phi$ with $\Phi$ quantifier-free; the universal theory $\mathrm{Th}_\forall(\mathcal{C})$ of a class $\mathcal{C}$ of groups is the set of universal sentences true in every group of $\mathcal{C}$, and it is decidable if some algorithm decides membership in it. A finitely generated group is lacunary hyperbolic if at least one of its asymptotic cones is a real tree. Let $\mathcal{H}$ be the class of all hyperbolic groups. Then (Theorem 1.3 of the source):

1. $\mathrm{Th}_\forall(\mathcal{H})$ is undecidable;
2. there exists a lacunary hyperbolic group $G$ with $\mathrm{Th}_\forall(G) = \mathrm{Th}_\forall(\mathcal{H})$; in particular $\mathrm{Th}_\forall(G)$ is undecidable.

By contrast, the universal theory of each single hyperbolic group is decidable (Sela for torsion-free hyperbolic groups, Dahmani and Guirardel in general), as the source recalls.

## Depends on

- [Word-hyperbolic groups](../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [The first-order language of groups](../../../Logic/model-theory/first-order-language-of-groups/group-language.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

None.

## Expansion

Every hyperbolic group is residually torsion of bounded exponent (Ivanov and Olshanskii), so by the source's Lemma 3.2 $\mathrm{Th}_\forall(\mathcal{T}) \subseteq \mathrm{Th}_\forall(\mathcal{H})$ for the class $\mathcal{T}$ of torsion groups, and $\mathrm{Th}_\forall(\mathcal{H}) \subseteq \mathrm{Th}_\forall(\mathcal{F})$ for the class $\mathcal{F}$ of finite groups, since finite groups are hyperbolic. Slobodskoi's lemma (Lemma 3.1 of the source: every theory $T$ with $\mathrm{Th}_\forall(\mathcal{T}) \subseteq T \subseteq \mathrm{Th}_\forall(\mathcal{F})$ is undecidable) gives clause 1. For clause 2 the source takes a lacunary hyperbolic group $G$ into which every hyperbolic group embeds (Proposition 3.5), so $\mathrm{Th}_\forall(G) \subseteq \mathrm{Th}_\forall(\mathcal{H})$, and Lemma 3.2 with Theorem 3.3 gives $\mathrm{Th}_\forall(\mathcal{H}) \subseteq \mathrm{Th}_\forall(G)$ for every lacunary hyperbolic group. A good expansion links pages for Slobodskoi's lemma, the residual torsion of hyperbolic groups and the embedding of all hyperbolic groups into one lacunary hyperbolic group.

## Sources

- D. Osin, "On the universal theory of torsion and lacunary hyperbolic groups", Groups – Complexity – Cryptology 1 (2009), no. 2 (the publisher metadata records no page range), https://doi.org/10.1515/GCC.2009.311; read in arXiv:0903.3978v2 (Theorem 1.3, Lemmas 3.1 and 3.2, Theorem 3.3 and Proposition 3.5 of arXiv:0903.3978v2).
