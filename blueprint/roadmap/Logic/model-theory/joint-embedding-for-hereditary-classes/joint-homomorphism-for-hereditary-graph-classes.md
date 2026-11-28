# Joint homomorphism for hereditary graph classes is undecidable

There is no algorithm that decides, given finitely many forbidden induced subgraphs, whether any two finite graphs avoiding them map homomorphically into a common such graph.

**Theorem (Braunfeld).** There is no algorithm that, given a finite set $\mathcal F$ of finite graphs, decides whether the hereditary graph class $\mathrm{Forb}(\mathcal F)$ of finite graphs with no induced subgraph isomorphic to a member of $\mathcal F$ has the [joint homomorphism property](joint-homomorphism-property.md), that is, whether for all $A, B \in \mathrm{Forb}(\mathcal F)$ some $C \in \mathrm{Forb}(\mathcal F)$ admits graph homomorphisms from $A$ and from $B$. This is Theorem 1.3 of arXiv:1903.11932v4, proved by a reduction from the tiling problem.

Graphs are in the language with the edge relation only. In a language with relations for both edges and non-edges the analogous statement follows directly from the undecidability of the joint embedding property, since the forbidden structures can be chosen so that every homomorphism is an embedding (Proposition 5.2 of the source); in the pure graph language more work is needed, because the JHP is not invariant under quantifier-free interdefinable changes of language. This answers a question of Bodirsky.

## Depends on

- [Joint homomorphism property](joint-homomorphism-property.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Joint embedding for hereditary graph classes is undecidable](joint-embedding-for-hereditary-graph-classes.md)
- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof modifies the construction for the joint embedding property so that homomorphisms from the two canonical models into a witness of the JHP are forced to be embeddings, so that such a witness also witnesses the JEP for them (proof of Theorem 5.1, by Theorem 5.13). It does not make every homomorphism between members an embedding: two nonadjacent vertices can still map to one vertex. The all-homomorphisms statement holds only in the language with relations for edges and non-edges (Proposition 5.2). Wheel graphs serve as gadgets: every proper homomorphic image of the wheel $W_5$ contains a copy of $K_4$ (Fact 5.4), and the construction uses this to keep homomorphisms between members of the class from collapsing the coding. For a tiling problem $\mathcal T$ the resulting class has the JHP iff $\mathcal T$ has a solution, as in the JEP construction.

## Sources

- S. Braunfeld, "The undecidability of joint embedding and joint homomorphism for hereditary graph classes", *Discrete Mathematics & Theoretical Computer Science* 21(2), Permutation Patterns 2018, 2019, paper 9, <https://doi.org/10.23638/DMTCS-21-2-9>; numbers from arXiv:1903.11932v4, <https://arxiv.org/abs/1903.11932v4>: Section 5: Theorem 5.1, Proposition 5.2, Definition 5.3, Fact 5.4 and Theorem 5.13 (the constructed class has the JHP iff the tiling problem has a solution).
- S. W. Braunfeld, *Infinite Limits of Finite-Dimensional Permutation Structures, and their Automorphism Groups: Between Model Theory and Combinatorics*, PhD dissertation, Rutgers, The State University of New Jersey, 2018; read as arXiv:1805.04219v1, <https://arxiv.org/abs/1805.04219v1>: Theorems 9.1.3, 9.6.1 and 9.6.17 of that version (the same result; Theorem 9.6.17 states that the constructed class has the JHP iff the tiling problem has a solution).
