# Level-3 semi-directed networks are encoded by quinnets

**Setting.** A *semi-directed network* on a leaf set $X$ is a mixed graph obtained from a rooted binary phylogenetic network by suppressing the root and undirecting all edges except those entering reticulation vertices. A *blob* is a maximal 2-edge-connected subgraph; a network is *level-$k$* if every blob contains at most $k$ reticulations. For $3 \le k \le |X|$, the *$k$-nets* of $N$ are the semi-directed networks it induces on $k$-subsets of $X$; 4-nets are *quarnets* and 5-nets *quinnets*. A class $\mathcal C$ is *encoded by $k$-nets* if any two networks in $\mathcal C$ with the same collection of $k$-nets (up to isomorphism) are isomorphic. The *generator* of a simple network is the multigraph left after deleting leaves and suppressing degree-2 vertices; its edges and parallel-edge pairs are its *sides*.

**Theorem.** Let $\mathcal L_3$ be the class of binary level-3 semi-directed networks.
1. $\mathcal L_3$ is encoded by quinnets.
2. $\mathcal L_3$ is encoded by quarnets modulo one ambiguity: reversing the top side of the blobs whose generator is of type 14 (one specific level-3 generator).

Moreover, a level-$k$ semi-directed generator has at most $3k - 2$ vertices and $4k - 3$ edges, and every strictly level-$k$ network has, for each $3 \le k' \le k$, a $k''$-net with $k'' \le k'$ that is not level-$(k'-1)$.

## Expansion

Quarnets determine the tree of blobs, so the problem reduces to simple networks (a single blob). For a simple level-$k$ network the $k$-nets determine the generator, $(k+1)$-nets determine which leaves hang on which side, and $(k+2)$-nets (or $(k+1)$-nets on parallel-edge sides) determine whether two leaves share a side and the order of leaves along each side. For level 3 these steps can mostly be carried out with quarnets, except that on the type-14 generator no four-leaf subnetwork distinguishes the two orientations of the top side; a fifth leaf breaks the symmetry. Level-1 and level-2 networks were already known to be encoded by quarnets.

## Sources

- N. Holtgrefe, K. T. Huber, L. van Iersel, V. Moulton, "Encoding level-3 semi-directed phylogenetic networks by quarnets and quinnets", arXiv:2610.07855 (2026), Corollary 2.6, Propositions 3.1, 3.3, 3.4 and 3.11, Theorem 4.5, <https://doi.org/10.48550/arXiv.2610.07855>.
