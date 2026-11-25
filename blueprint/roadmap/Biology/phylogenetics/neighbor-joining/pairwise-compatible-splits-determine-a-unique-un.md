# Pairwise compatible splits determine a unique unrooted X-tree

Let $X$ be a finite set with $|X|\ge2$. A split of $X$ is an unordered pair $\{A,X\setminus A\}$ with $A$ and $X\setminus A$ nonempty; it is trivial if one side is a singleton. Two splits $A\mid A^c$ and $B\mid B^c$ are [compatible](../splits-compatibility-ultrametrics-and-upgma/compatible.md) if at least one of $A\cap B$, $A\cap B^c$, $A^c\cap B$, $A^c\cap B^c$ is empty. An $X$-tree is a finite tree $T$ with a map $\iota:X\to V(T)$ whose image contains every vertex of degree at most $2$; each edge induces the split of $X$ into the taxa of the two components left by deleting it, and $\Sigma(T)$ denotes the set of these splits.

Let $\mathcal S$ be a set of nontrivial splits of $X$ that are pairwise compatible, and let $\mathcal S^+$ be $\mathcal S$ together with all trivial splits. Then there is an $X$-tree $T$ with $\Sigma(T)=\mathcal S^+$, and it is unique up to isomorphism: if $T'$ is another $X$-tree with $\Sigma(T')=\mathcal S^+$, there is a tree isomorphism $\phi:T\to T'$ with $\phi\circ\iota=\iota'$. Conversely, the splits of any $X$-tree are pairwise compatible. Two splits that are not compatible are never both splits of one $X$-tree.

## Depends on

- [Compatible splits](../splits-compatibility-ultrametrics-and-upgma/compatible.md)

## Proof depends on

- [Splits-equivalence theorem](../splits-compatibility-ultrametrics-and-upgma/splits-equivalence.md)
- [Splits of two tree edges are compatible](side-compat.md)

## Expansion

A proof page must establish:

- existence by induction on $|\mathcal S|$: the star tree realizes the trivial splits, and a split compatible with all splits of the current tree is added by refining exactly one vertex into two joined by a new edge;
- uniqueness, for instance by recovering vertices and edges from $\mathcal S^+$, so that two $X$-trees with the same split set are isomorphic by a map fixing the labels;
- compatibility of the splits of an $X$-tree (two edges of a tree induce compatible splits);
- a five-leaf check of the induction step, and the rejection of an incompatible pair such as $\{1,2\}\mid\{3,4,5\}$ and $\{1,3\}\mid\{2,4,5\}$.

The [splits-equivalence theorem](../splits-compatibility-ultrametrics-and-upgma/splits-equivalence.md) states the existence of an unrooted binary tree whose splits contain $\mathcal S$; the result here is the exact, unique realization by a not necessarily binary $X$-tree.

## Sources

- C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003) (splits-equivalence theorem).
- P. Buneman, *The recovery of trees from measures of dissimilarity*, in Mathematics in the Archaeological and Historical Sciences, Edinburgh University Press (1971), 387–395 (tree recovery; background).
