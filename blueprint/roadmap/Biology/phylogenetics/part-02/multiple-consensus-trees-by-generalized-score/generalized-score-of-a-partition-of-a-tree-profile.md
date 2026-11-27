# Generalized score of a partition of a tree profile

**Setting.** A profile $\pi$ is a list of $m$ unrooted phylogenetic trees on the same taxon set $X$, $|X| = n$; each tree is identified with the set of bipartitions (splits) given by its internal edges. A bipartition $P_i$ has support $m_i$, the number of trees of the profile containing it, and is a **majority** bipartition if $m_i > m/2$. The majority-rule consensus tree $C$ of $\pi$ consists of all majority bipartitions, and its weight is

$$W_\pi(C) = \sum_{P_i \in C} m_i.$$

**Definition.** For a partition $\mathcal P_\pi = \{\pi_1,\dots,\pi_k\}$ of the profile into classes of sizes $p_1,\dots,p_k$ with majority consensus trees $C_1,\dots,C_k$, the **generalized score** is

$$W^k(\mathcal P_\pi) = \sum_{i=1}^k p_i\,W_{\pi_i}(C_i).$$

The single-class value $W^1 = m\,W_\pi(C)$ is the reference; the atomic partition into singletons gives $W^m = \sum_{i=1}^m n_i \le m(n-3)$, where $n_i$ is the number of internal edges of tree $i$. The profile admits a single, multiple or atomic consensus according to which partition maximizes $W$.

**Proposition.** Two trees with $n_1$ and $n_2$ internal edges sharing $k$ of them satisfy $W^1 = 4k$ and $W^2 = n_1 + n_2$, so they admit a single consensus iff $k > (n_1+n_2)/4$; for two fully resolved trees ($n_1 = n_2 = n-3$) this means sharing more than half of their internal edges.

## Depends on

- [The majority-rule consensus tree](../../splits-compatibility-ultrametrics-and-upgma/exists-tree-majority-splits-subset.md)

## Expansion

The score is a vote: each of the $p_i$ trees in a class adopts the class consensus as its representative and contributes its weight, so a majority edge counts both through its support and through the class size, which makes the criterion quadratic and rewards splitting a profile when sub-profiles have strongly supported but mutually incompatible consensus trees. For two trees, only shared edges are majority edges, each with support $2$, so $W_\pi(C) = 2k$ and $W^1 = 2\cdot 2k$. Maximizing over all partitions is combinatorial; in practice nested partitions are built by average-linkage clustering of Robinson–Foulds or quartet similarities, or by greedily merging the pair of classes that most increases the score, and the best level of the hierarchy is kept. A profile with no majority edge (star consensus) is always better represented atomically.

## Sources

- A. Guénoche, "Multiple consensus trees: a method to separate divergent genes", BMC Bioinformatics 14 (2013) 46, Background, Definition 1, Examples 1–2, Proposition 1 and Methods, <https://doi.org/10.1186/1471-2105-14-46>, PMCID PMC3599424.
