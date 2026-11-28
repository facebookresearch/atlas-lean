# Fixed-parameter tractability and NP-completeness of orienting a network into a network class

**Problem.** Let $C$ be a class of rooted binary directed phylogenetic networks (for example tree-child, stack-free, tree-based, orchard, valid or reticulation-visible networks). *$C$-Orientation* asks, for an undirected binary phylogenetic network $N$ with no information about root or reticulations, for an orientation of $N$ that belongs to $C$, or the answer NO. Here an orientation places the root on some edge and directs all edges so that the result is a rooted binary phylogenetic network.

Call $C$ *blob-determined* if a network is in $C$ exactly when every network induced by one of its blobs (maximal 2-connected components, with leaves attached to vertices that lost children) is in $C$; *leaf-addable* if adding leaves to a member of $C$ keeps it in $C$; and *$\ell$-chain reducible* if, roughly, long chains of leaves on one side of the generator of a blob can be shortened to $\ell$ leaves without changing which edges can carry the root of a $C$-orientation.

**Theorem.**

1. *(Exhaustive algorithm.)* For $N$ with $n$ vertices and reticulation number $k=|E|-|V|+1$, trying every root edge and every $k$-set of reticulations and running the unique constrained orientation solves $C$-Orientation in $O(n^{k+1}(n+f_C(n,k)))$ time, where $f_C(n,k)$ is the time to test membership in $C$.
2. *(FPT in the reticulation number.)* If $C$ is $\ell$-chain reducible, leaf-addable and blob-determined, and the membership test on networks of bounded size is computable, then $C$-Orientation is fixed-parameter tractable with parameter the reticulation number of $N$.
3. *(FPT in the level.)* Under the same hypotheses (for any fixed $\ell$), $C$-Orientation is fixed-parameter tractable with parameter the level of $N$ (the maximum reticulation number of a blob).
4. *(Concrete classes.)* The level-parameterized algorithm applies when $C$ is the class of tree-child, stack-free, tree-based, reticulation-visible, valid, or orchard networks.
5. *(Hardness.)* Deciding whether an undirected binary phylogenetic network has a tree-based orientation (*Tree-Based Orientation*) is NP-complete.

## Proof depends on

- [Constrained orientation of undirected phylogenetic networks by degree cuts](constrained-orientation-by-degree-cuts.md)

## Expansion

Item 1 uses that once the root edge and the reticulation set are fixed the orientation, if any, is unique and computable in linear time. Blob-determinedness lets the algorithm treat each blob separately, and the remaining difficulty is that a blob can carry arbitrarily many pendant leaves and trees. Leaf-addability and $\ell$-chain reducibility show that replacing each long chain of leaves on a side of the blob by $\ell$ leaves preserves the set of admissible root edges, so each blob shrinks to size bounded by a function of its reticulation number (at most $8\ell(k-1)$ vertices on the sides), and the exhaustive algorithm then runs in time depending only on the parameter. The blob results are combined along the tree of blobs to obtain the level version. NP-hardness of Tree-Based Orientation is by reduction from deciding whether an undirected binary network is tree-based. The two problems differ: some undirected networks are not tree-based yet admit a tree-based orientation, because the base tree of the orientation need not induce a base tree of the undirected graph.

## Sources

- K. T. Huber, L. van Iersel, R. Janssen, M. Jones, V. Moulton, Y. Murakami, C. Semple, "Orienting undirected phylogenetic networks", arXiv:1906.07430 (2019), Section "Orientations within a specific subclass of directed binary phylogenetic networks" (Lemma 2, Definitions 3, 4 and 5, Theorems 4 and 5), Section "Specific classes" (Theorem 6), and Appendix (Theorem 7; Section "Undirected tree-based networks", Theorem 8), <https://doi.org/10.48550/arXiv.1906.07430>.
