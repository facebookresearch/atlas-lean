# Number of delimited species trees

A **delimited species tree** on a set $X$ of $n$ labelled samples is a partition of $X$ into $k \ge 1$ non-empty blocks (species), together with a rooted binary tree whose leaves are the $k$ blocks (no tree is needed when $k = 1$).

**Proposition.** The number of delimited species trees on $n$ samples is

$$D(n) = \sum_{k=1}^{n} \left\{ {n \atop k} \right\} (2k - 3)!!,$$

where $\left\{ {n \atop k} \right\}$ is the Stirling number of the second kind, $(2k - 3)!! = 1 \cdot 3 \cdots (2k - 3)$ is the number of rooted binary trees on $k$ labelled leaves, and $(-1)!! = 1$. In particular the number of ways to split one species of $m$ samples into two species is $\left\{ {m \atop 2} \right\} = 2^{m-1} - 1$.

Values: $D(20) \approx 6.03 \times 10^{23}$; splitting a species of $25$ samples into two admits $2^{24} - 1 = 16{,}777{,}215$ assignments.

## Proof depends on

- [Schröder's count of rooted binary phylogenetic trees](../../../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-rooted-binary-tree.md)

## Expansion

Choose the partition into $k$ species in $\left\{ {n \atop k} \right\}$ ways and then a rooted binary tree on the $k$ labelled species in $(2k-3)!!$ ways; the choices are independent, and summing over $k$ gives $D(n)$. For two blocks, each of the $2^m$ subsets and its complement give the same unordered partition, and the empty set is excluded, so there are $(2^m - 2)/2 = 2^{m-1} - 1$ partitions. The super-exponential growth of $D(n)$ (already $\approx 6.03 \times 10^{23}$ for 20 samples, as opposed to comparing two prespecified hypotheses) is what forces heuristic search (subtree pruning and regrafting, rerooting, merging sister species, splitting species, and moving guide-tree clades of samples between species) rather than exhaustive evaluation, and the size of the split move is why only a subset of assignments is examined at each step.

## Sources

- B. C. O'Meara, "New heuristic methods for joint species delimitation and species tree inference", Systematic Biology 59 (2010), 59–73, sections "Approach 1: KC delimitation" and "Search Strategy", <https://doi.org/10.1093/sysbio/syp077> (PMC5841455).
