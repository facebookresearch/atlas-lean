# Whether two graphs have equal homomorphism counts from all planar graphs is undecidable

No algorithm decides, given two finite simple graphs $G$ and $H$, whether some planar graph $K$ has a different number of homomorphisms into $G$ than into $H$.

For finite simple graphs $K$ and $G$, $\hom(K, G)$ is the number of homomorphisms from $K$ to $G$, that is, of maps $V(K) \to V(G)$ that send adjacent vertices to adjacent vertices. Graphs $G$ and $H$ are *planar isomorphic* if $\hom(K, G) = \hom(K, H)$ for every [planar](../../planar-graphs-and-minors/straight-line-planar-drawings/is-planar.md) graph $K$ (planar graphs being, by Fáry's theorem, exactly those with straight-line planar drawings).

**Theorem (Mančinska and Roberson).** The problem of deciding, for two input graphs $G$ and $H$, whether there exists a planar graph $K$ with $\hom(K, G) \ne \hom(K, H)$ is undecidable (Corollary 7.17 of the source).

The source's graphs may have loops (Section 2.1), and Corollary 7.17 is stated for such graphs. The statement for simple graphs follows in the same way: the undecidability of quantum isomorphism that the corollary rests on was proved by Atserias et al. for graphs without loops (Remark 2.20 of the source), Theorem 7.16 applies to them, and a homomorphism maps a vertex with a loop only to a vertex with a loop (the note after Definition 2.1), so a planar graph with a loop has no homomorphism into a graph without loops and the condition over all planar graphs is the same as the condition over simple ones.

By a theorem of Lovász, counts from all graphs $K$ determine $G$ up to isomorphism; restricting $K$ to planar graphs gives a strictly coarser relation, and the theorem shows it cannot be decided. It suffices to compare connected planar graphs $K$, since counts are multiplicative over connected components.

## Depends on

- [Finite simple graph](../../planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Straight-line planar graph](../../planar-graphs-and-minors/straight-line-planar-drawings/is-planar.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source proves that $G$ and $H$ are quantum isomorphic (there is a perfect quantum strategy, in the commuting-operator framework, for the $(G, H)$-isomorphism game) if and only if they are planar isomorphic (Theorem 7.16 of the version read), through a characterization of the intertwiners of the quantum automorphism group of a graph by planar bilabeled graphs. Combined with the undecidability of quantum isomorphism, which the source attributes to Atserias, Mančinska, Roberson, Šámal, Severini and Varvitsiotis, this gives the corollary. A good expansion links the equivalence of quantum and planar isomorphism and the undecidability of quantum isomorphism, both for graphs without loops.

## Sources

- L. Mančinska and D. E. Roberson, "Quantum isomorphism is equivalent to equality of homomorphism counts from planar graphs", in *2020 IEEE 61st Annual Symposium on Foundations of Computer Science (FOCS 2020)*, IEEE, 2020, pp. 661–672, doi:10.1109/FOCS46700.2020.00067; read in arXiv:1910.06958v2: Corollary 7.17 (the undecidability statement), Theorem 7.16, Definition 7.1 (planar isomorphism) and Lemma 7.10 (reduction to connected planar graphs) in Section 7, and Section 2.1 (graphs may have loops), the note after Definition 2.1 and Remark 2.20, in the numbering of that version.
- A. Atserias, L. Mančinska, D. E. Roberson, R. Šámal, S. Severini and A. Varvitsiotis, "Quantum and non-signalling graph isomorphisms", *Journal of Combinatorial Theory, Series B* 136:289–328, 2019, doi:10.1016/j.jctb.2018.11.002: the undecidability of quantum isomorphism, cited by the source above (not read here).
