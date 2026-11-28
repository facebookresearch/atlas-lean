# Derived-mutation distance and tree reconstruction

Let $\mathcal T$ be a rooted binary tree on haplotypes $1, \dots, n$ with known ancestral and derived alleles at a set of sites, each site carrying one mutation on one branch (infinite-sites model, no recombination). Define the asymmetric *derived-mutation distance*

$$d(i, j) = \#\{\text{sites derived in } i \text{ and ancestral in } j\}.$$

**Proposition.** $d(i, j)$ equals the number of mutations on the path from haplotype $i$ up to the most recent common ancestor of $i$ and $j$. Consequently, along row $i$, $d(i, \cdot)$ is nondecreasing in the time at which $j$ joins the lineage of $i$: if $j$ coalesces with $i$ strictly before $j'$ does, then $d(i, j) \le d(i, j')$, with strict inequality when some mutation lies on the lineage of $i$ between the two coalescence events.

**Agglomerative tree building.** Call current clades $A$ and $B$ *mutual nearest* if $d(a, b) < d(a, c)$ for all $a \in A$, $b \in B$ and $c$ in any other current clade, and symmetrically with $A$ and $B$ exchanged. When every branch carries at least one mutation, a pair of mutual nearest clades always exists and they are siblings in $\mathcal T$; merging them, replacing their rows and columns by clade-size-weighted averages, and repeating reconstructs the topology of $\mathcal T$. In the presence of recombination, $d$ is replaced by a position-specific matrix obtained from rescaled log posterior copying probabilities of a Li–Stephens hidden Markov model with ancestral/derived emissions; it reduces to the count above in the limit of no recombination.

## Depends on

- [The Li–Stephens copying model](../../../population-structure/li-stephens-haplotype-copying-model/hmm.md)

## Expansion

A site is derived in $i$ and ancestral in $j$ exactly when its mutation lies on the lineage of $i$ below $\mathrm{MRCA}(i, j)$; mutations above the MRCA are shared by both, and those on the $j$ side are derived in $j$ only. As $j$ ranges over haplotypes joining $i$'s lineage at successively older nodes, the path from $i$ to the MRCA only lengthens. Sibling clades are mutual nearest because the branch above their parent carries a mutation (unless the parent is the root, when they are the last two clades). Conversely, if $A$ and $B$ are mutual nearest but not siblings, the sibling subtree of one of them contains the other together with a third current clade, and the strict inequality fails in one of the two directions. The weighted row and column updates preserve the form $d(A, j) = (\text{mutations from } A \text{ to } \mathrm{MRCA}(A, j))$ up to an additive constant per row, so the argument repeats.

## Sources

- L. Speidel, M. Forest, S. Shi and S. R. Myers, *A method for genome-wide genealogy estimation for thousands of samples*, Nat. Genet. 51 (2019), 1321–1329, <https://doi.org/10.1038/s41588-019-0484-x>, PMCID PMC7610517 (Online Methods: position-specific distance matrices, tree builder).
