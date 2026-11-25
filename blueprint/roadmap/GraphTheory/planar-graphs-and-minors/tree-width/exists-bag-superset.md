# Every clique lies in a bag

Let $(T, (V_t))$ be a tree-decomposition of a graph $G$ and let $K$ be a finite set of pairwise
adjacent vertices of $G$. Then some bag $V_t$ contains $K$.

The source derives this from its Lemma 12.3.4 (a vertex set contained in no bag contains two
vertices separated by an adhesion set). A Helly-type argument also works: adding
the vertices of $K$ one at a time, take the node of the subtree of bags containing the new vertex
that is nearest, in $T$, to a bag containing the vertices already treated; by (T3) its bag
contains them all.

## Background

- [Tree-decomposition](tree-decomposition.md): the conditions (T1)–(T3) used in the proof.

## Sources

- Reinhard Diestel, *Graph Theory*, 6th edition, author's online preview of Chapter 12 (PDF dated 28 June 2024), https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch12.pdf, Corollary 12.3.5.
