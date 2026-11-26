# Tree-width does not increase under taking minors

Let $H$ be a minor of a finite graph $G$. If $G$ has tree-width at most $k$, then so does $H$.
Minors are the relation of [graph minors](../graph-minors/is-minor.md): finite sequences of
isomorphisms, vertex deletions, edge deletions and edge contractions.

The proof in the source passes a tree-decomposition to subgraphs (Lemma 12.3.2) and to
contractions (Lemma 12.3.3, which uses the separation property of tree-decompositions, Lemma
12.3.1).

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Lemma 12.4.1.
