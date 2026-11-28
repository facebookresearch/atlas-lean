# Being the fundamental group of a closed 3-manifold is undecidable for finite presentations

No algorithm decides, given a finite presentation of a group, whether the group is isomorphic to the fundamental group of a closed 3-manifold.

A *closed 3-manifold* is a compact, connected 3-manifold without boundary (in the source all 3-manifolds are compact and connected), as on the page [closed topological 3-manifold](../../../../Topology/manifolds-geometric-topology/linearity-of-3-manifold-groups/closed3-manifold.md); a group is a *closed 3-manifold group* if it is isomorphic to the fundamental group of one. An instance is a finite presentation $\langle X \mid R \rangle$.

**Theorem (Aschenbrenner, Friedl and Wilton).** There is no algorithm that takes as input a finite presentation for a group $\pi$ and decides whether $\pi$ is the fundamental group of a closed $3$-manifold (Lemma 3.4 of arXiv:1405.6274v2).

In the other direction, the source gives a procedure that, given a finite presentation of a group that is a closed 3-manifold group, eventually confirms this; on other inputs it need not terminate. So the set of finite presentations of closed 3-manifold groups is recursively enumerable but not recursive.

## Depends on

- [Group](../../../group-basics/group.md)
- [Closed topological 3-manifold](../../../../Topology/manifolds-geometric-topology/linearity-of-3-manifold-groups/closed3-manifold.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Triviality of finitely presented groups is undecidable](triviality-of-finite-presentations-undecidable.md)

## Expansion

The trivial group is the fundamental group of the 3-sphere. Triviality is undecidable for finite presentations in general, but it is decidable within the class of closed 3-manifold groups (Corollary 4.9 of the source, from the uniform solution to the word problem for 3-manifold groups, Theorem 4.1). If being a closed 3-manifold group were decidable, one could first test whether a given presentation defines a closed 3-manifold group, reject it if not, and otherwise decide its triviality within that class, which would decide triviality for all finite presentations. Alternatively, being a closed 3-manifold group is a Markov property in Rabin's sense, because some finitely presented groups embed in no 3-manifold group: for example $\mathbb{Z}^4$, or the Baumslag–Solitar group $\mathrm{BS}(2,3)$, which is not residually finite, whereas every 3-manifold group is (Theorem 4.2 of the source), so the [Adian–Rabin theorem](adian-rabin-theorem.md) applies. A complete expansion links a page for the decidability of triviality among closed 3-manifold groups.

## Sources

- M. Aschenbrenner, S. Friedl and H. Wilton, "Decision problems for 3-manifolds and their fundamental groups", in *Interactions between Low-Dimensional Topology and Mapping Class Groups*, Geometry & Topology Monographs 19, 2015, pp. 201–236, doi:10.2140/gtm.2015.19.201; read as arXiv:1405.6274v2, <https://arxiv.org/abs/1405.6274v2>: Lemma 3.3 and the procedure in its proof, Lemma 3.4 and the discussion following it, Theorem 4.2 and Corollary 4.9, with the numbering of that version.
