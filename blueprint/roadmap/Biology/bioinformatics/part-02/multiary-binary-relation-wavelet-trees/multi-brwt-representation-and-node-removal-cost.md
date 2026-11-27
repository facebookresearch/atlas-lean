# Multi-BRWT representation of a genome graph annotation

**Setting.** A genome graph annotation assigns to each object $v \in V$ (a $k$-mer of a de Bruijn graph) a set of labels $\ell(v) \subset L$ (samples, genomes). It is a binary relation $\mathcal{R} \subset V \times L$, equivalently a matrix $A \in \{0,1\}^{|V| \times |L|}$; the required queries are the labels of an object, the objects of a label, and membership of a pair.

**BRWT.** The binary relation wavelet tree stores at its root the index vector $I$ with $I_i = \bigvee_j A_{ij}$ (row-wise OR of all columns), deletes the all-zero rows, splits the remaining matrix column-wise into two submatrices passed to the two children, and recurses until a node holds a single column. Only the index vectors are stored; a matrix entry is recovered by descending the tree and translating row indices by rank queries on the index vectors.

**Multi-BRWT.** The generalization allows any arity and any assignment of columns to children (a rooted tree whose $|L|$ leaves are the columns). With $\mathrm{Size}(I)$ the size in bits of a compressed bit vector (for instance $\mathrm{Size}(I) \approx \lceil \log_2 \binom{n}{m} \rceil$ for an RRR vector of length $n$ with $m$ set bits), the size of a tree $T$ with node set $N$ is

$$\mathrm{Size}(T) = \sum_{i \in N} \mathrm{Size}(I_i),$$

and the Multi-BRWT problem asks for $T^* = \arg\min_T \mathrm{Size}(T)$; restricted to binary trees with uncompressed index vectors it is NP-hard.

**Node removal cost.** Suppose $\mathrm{Size}$ depends only on the length and the number of set bits of a vector, $\mathrm{Size}(I) = \mathrm{Size}(n, m)$. Removing an internal node $v$ (index vector of length $n_v$ with $m_v$ set bits) and reattaching its children $c$ (vectors of length $n_c$ with $m_c$ set bits) to the parent of $v$ replaces each child vector by one of length $n_v$ with $m_c$ set bits, so the change in total size is

$$\mathrm{CostRem}(v) = \sum_{c \in \mathrm{Children}(v)} \mathrm{Size}(n_v, m_c) - \Big( \mathrm{Size}(n_v, m_v) + \sum_{c \in \mathrm{Children}(v)} \mathrm{Size}(n_c, m_c) \Big),$$

and $v$ is removed when this cost is negative. A greedy construction first builds a binary tree by repeatedly matching the pair of (aggregated) columns with the largest intersection, then prunes internal nodes bottom-up with this criterion.

## Depends on

- [Succinct rank and select](../../../../ComputerScience/data-structures/range-query-structures/advanced-data-structures/succinct-rank-and-select.md)

## Expansion

A child of $v$ stores bits only for rows that are non-zero in $v$, i.e. a vector of length $m_v$ equal to the number of set bits of $v$; after removing $v$ it must be indexed by the rows of $v$'s parent, of which there are $n_v$. The criterion trades the cost of storing $v$ against the cost of lengthening its children, and it can be evaluated from stored lengths and popcounts without rebuilding the tree. Grouping similar columns under a common ancestor makes the ancestor's index vector sparse relative to the union, which is where the compression gain comes from when labels are correlated.

## Sources

- M. Karasikov, H. Mustafa, A. Joudaki, S. Javadzadeh-No, G. Rätsch, A. Kahles, "Sparse binary relation representations for genome graph annotation", Journal of Computational Biology 27(4) (2020) 626-639, Sections 2.2.5 and 2.3 (Equations 2-5, Lemma 1), <https://doi.org/10.1089/cmb.2019.0324> (PMC7185347).
