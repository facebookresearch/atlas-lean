# Local-search approximation for maximum conflict-free triangle packing

**Setting.** For a multiset $L = \{a_1, \dots, a_n\}$ of subclonal frequencies, triangles $(k, \{i,j\})$ with $a_i + a_j = a_k$ and conflict-freeness are as in the [binary tree partition problem](conflict-free-triangle-characterization-and-strong-np-completeness-of-binary-tree-partitions.md). The **max-BTP problem** asks for a largest conflict-free set of triangles of $L$; such a set records partial ancestry among the mutation clusters, and $L$ has a binary tree partition exactly when the optimum equals $(n-1)/2$.

**Local search.** Fix an integer $t \ge 1$. Start from any conflict-free set of triangles and, while possible, replace some $s \le t$ triangles of the current set by $s + 1$ triangles of $L$ so that the new set is still conflict-free.

**Theorem.** For every $\delta > 0$ there is a constant $t$ such that the local search above runs in polynomial time and returns a conflict-free set of size at least $(2/3 - \delta)\,\mathrm{OPT}$, where $\mathrm{OPT}$ is the maximum size of a conflict-free set of triangles of $L$.

Moreover, if a max-BTP solution on $m$ elements has $\Delta$ triangles, a binary tree partition of $L$ augmented by $m - 1 - 2\Delta$ additional (auxiliary) nodes can be constructed.

## Depends on

- [Conflict-free triangle characterization and strong NP-completeness of binary tree partitions](conflict-free-triangle-characterization-and-strong-np-completeness-of-binary-tree-partitions.md)

## Expansion

Encode a triangle $(k, \{i,j\})$ as the 3-element set $\{P_k, T_i, T_j\}$ over the ground set of "peak slots" $P_1, \dots, P_n$ and "tail slots" $T_1, \dots, T_n$. Two triangles conflict exactly when they share a peak or a tail, that is, when their 3-sets intersect, so conflict-free sets of triangles are exactly packings of disjoint 3-sets. Each improvement step increases the size by one and the size is at most $(n-1)/2$, so there are at most $n$ steps, each examining $O(n^{3(2t+1)})$ candidate exchanges for fixed $t$. The Hurkens–Schrijver bound for $k$-set packing states that a packing admitting no improving exchange of size at most $t$ has size at least $(2/k - \varepsilon_t)$ times the optimum with $\varepsilon_t \to 0$ as $t \to \infty$; with $k = 3$ this gives the factor $2/3 - \delta$.

## Sources

- I. Hajirasouliha, A. Mahmoody, B. J. Raphael, "A combinatorial approach for analyzing intra-tumor heterogeneity from high-throughput sequencing data", Bioinformatics (2014), Section 4 (local search and Theorem 6), <https://doi.org/10.1093/bioinformatics/btu284>, PMCID PMC4058927.
- C. A. J. Hurkens, A. Schrijver, "On the size of systems of sets every t of which have an SDR, with an application to the worst-case ratio of heuristics for packing problems", SIAM Journal on Discrete Mathematics (1989), <https://doi.org/10.1137/0402008>.
