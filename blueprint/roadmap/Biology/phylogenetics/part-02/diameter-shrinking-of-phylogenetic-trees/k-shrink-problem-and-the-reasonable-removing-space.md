# The k-shrink problem and the reasonable removing space

Let $t$ be an unrooted tree with leaf set $\mathcal{L}$, $|\mathcal{L}| = n$, and nonnegative branch lengths, and let $\delta(a,b)$ be the path length between leaves $a,b$. For $A \subseteq \mathcal{L}$ write $t|_A$ for the restriction of $t$ to $A$ and $t \setminus a = t|_{\mathcal{L}\setminus\{a\}}$. The **diameter** of $t$ is $\max_{a,b}\delta(a,b)$; a pair attaining it is a **diameter pair**, $P(t)$ is the set of diameter pairs, and $D(t) = \{a : \exists x,\ (a,x) \in P(t)\}$ is the **diameter set**.

**The k-shrink problem.** Given $t$ and $1 \le k \le n$, find for every $1 \le i \le k$ a set $R^*_i(t) \subset \mathcal{L}$ of $i$ leaves whose removal minimizes the diameter of $t|_{\mathcal{L}\setminus R^*_i(t)}$.

A removal of leaf $a$ is **reasonable** if $a \in D(t)$; an $i$-set of leaves is a **reasonable $i$-removing set** if some ordering of it is a chain of reasonable removals, and the set of these is the **$i$-removing space** $S_i(t)$. The tree is **singly paired** if $|P(t|_A)| = 1$ for every $A \subseteq \mathcal{L}$.

1. (Persistence of diameter leaves.) If $a \in D(t)$ then $D(t)\setminus\{a\} \subseteq D(t\setminus a)$.
2. (Optimality of the reasonable space.) If $t$ is singly paired, then for every $k>0$ every optimal removing set lies in the reasonable space: $R^*_k(t) \in S_k(t)$.
3. (Linear width.) If $t$ is singly paired, then $|S_k(t)| = k+1$, so the reasonable search DAG up to level $k$ has $O(k^2)$ nodes.
4. (Arbitrary tie-breaking.) For any tree $t$, any $k$, and any diameter pair $(a,b) \in P(t)$, the subset of $S_k(t)$ whose members contain $a$ or $b$ (a pair-restricted removing space) contains at least one optimal $k$-removing set.

Consequently, after a linear-time preprocessing that stores, at every node of an arbitrarily rooted copy of $t$, the farthest descendant leaf and the best two-branch distance, all optimal sets $R^*_1(t),\dots,R^*_k(t)$ can be computed in $O(k^2 h + n)$ time, where $h$ is the height of the rooted tree.

## Depends on

- [Tree metrics](../../splits-compatibility-ultrametrics-and-upgma/is-tree-metric.md)

## Expansion

Only removing a diameter leaf can shrink the diameter, and removing one end of a diameter pair leaves the other end on-diameter (item 1). Building the removing space row by row, two sibling nodes always share a child, so row $i$ has $i+1$ nodes rather than $2^i$ (item 3). Greedy removal is not optimal, but searching this DAG is. When diameter pairs are tied, the tree has a unique midpoint that partitions $D(t)$ into diameter groups; the diameter can only decrease once all but one group is removed, and every such minimally shrunk tree is reachable from any pair-restricted space, which justifies breaking ties arbitrarily (item 4). The proportional diameter reductions along the optimal sequence are then screened with a tail test at a false-positive level $\alpha$, per tree, pooled over gene trees, or per species, to flag outlier long branches.

## Sources

- U. Mai and S. Mirarab, "TreeShrink: fast and accurate detection of outlier long branches in collections of phylogenetic trees", BMC Genomics 19 (Suppl 5) (2018), 272, Methods, Proposition 1, Theorems 1–3, Corollaries 1–2 and Proposition 2, <https://doi.org/10.1186/s12864-018-4620-2>, PMCID: PMC5998883.
