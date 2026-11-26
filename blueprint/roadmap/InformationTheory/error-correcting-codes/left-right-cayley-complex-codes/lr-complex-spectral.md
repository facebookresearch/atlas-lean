# Spectral expansion of the two Cayley graphs implies square-complex expansion

Let $X = \mathrm{Cay}^2(A, G, B)$ with $|A| = |B| = \Delta$ and suppose the Cayley graphs $\mathrm{Cay}(G, A)$ and $\mathrm{Cay}(G, B)$ are both $\lambda$-spectral expanders, i.e. all nontrivial eigenvalues of their adjacency matrices have absolute value at most $\lambda$. Consider the graph on $A$-edges of $X$ in which two $A$-edges are adjacent when they are opposite sides of a square. Then this graph is a disjoint union of copies of a $\Delta$-regular graph each isomorphic to a cover of $\mathrm{Cay}(G, B)$ and in particular has all nontrivial eigenvalues at most $\lambda$ in absolute value on each component; symmetrically for $B$-edges. Consequently, for sets $S \subseteq G$ and $T \subseteq E_A$, the number of squares incident to both is at most $\frac{\Delta^2}{|G|}|S||T|/\Delta + \lambda\sqrt{|S||T|}$ up to normalization (an expander mixing lemma for squares).

## Proof sketch

Moving across a square from the $A$-edge $\{g, ag\}$ to the opposite $A$-edge $\{gb, agb\}$ is right multiplication by $b$, which commutes with the left action of $A$; hence the parallel-edge graph is a Cayley-type graph for right multiplication by $B$, and its spectrum is contained in that of $\mathrm{Cay}(G, B)$ by a lifting argument. The mixing lemma follows from the standard expander mixing lemma applied to this graph.

## Depends on

- [Left-right Cayley complexes](left-right-cayley-complex.md)
- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Proof depends on

- [Left-right Cayley complexes](left-right-cayley-complex.md)
- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
