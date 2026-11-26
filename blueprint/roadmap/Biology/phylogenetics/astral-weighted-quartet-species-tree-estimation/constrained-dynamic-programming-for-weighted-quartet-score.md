# Constrained dynamic programming for the weighted quartet score

Let $\mathcal G = (g_1, \dots, g_k)$ be a family of binary gene trees on a set $L$ of $n \ge 4$ taxa, indexed by locus so that two loci with the same topology count twice, and let $w$ be the [tripartition weight](tripartition-shared-quartet-count.md) it defines. Fix a set $X$ of bipartitions of $L$ that contains every trivial bipartition $\{x\} \mid L \setminus \{x\}$, and let $X' = \{A : A \mid L \setminus A \in X\}$ be the set of all their sides (so $L \notin X'$). ASTRAL computes $V(\{x\}) = 0$ for every taxon $x$, then, for every $A \in X'$ with $|A| \ge 2$,

$$V(A) = \max_{A' \subset A \,:\, A' \in X',\ A \setminus A' \in X'} \Big\{ V(A') + V(A \setminus A') + w\big(A' \mid A \setminus A' \mid L \setminus A\big) \Big\},$$

where the third part $L \setminus A$ is nonempty because $A \ne L$, and finally, at the root,

$$V(L) = \max_{A' \in X'} \big\{ V(A') + V(L \setminus A') \big\},$$

with no tripartition term: the root of the rooted tree built by the recursion is not a node of the unrooted species tree. A maximum over an empty set is $-\infty$.

**Proposition (what the recursion computes).** $V(L) > -\infty$ if and only if some unrooted binary tree on $L$ has all its bipartitions in $X$. In that case the maximum of the weighted quartet score over such trees is $V(L)/2$, and an optimal tree is recovered by backtracking from $L$. The accumulator $V(L)$ is the sum of $w$ over the $n - 2$ internal nodes of the tree, each node of the unrooted tree corresponding to one non-root cluster of the rooted tree with its tripartition $A' \mid A \setminus A' \mid L \setminus A$.

**Theorem 1 (consistency).** Let $S$ be an unrooted binary species tree on $L$ with all internal branch lengths positive (in coalescent units), and let $g_1, g_2, \dots$ be independent true (not estimated) gene trees, each drawn from the multispecies coalescent on $S$ with one lineage per taxon. For each $k$ let $X_0^{(k)}$ be the set of bipartitions found in $g_1, \dots, g_k$ and let $X^{(k)} \supseteq X_0^{(k)}$ be the set given to ASTRAL. Then, as $k \to \infty$, the probability that every tree returned by ASTRAL on $(g_1, \dots, g_k)$ and $X^{(k)}$ is the unrooted topology of $S$ tends to one.

**Theorem 2 (running time).** The running time of ASTRAL-II is $O(nk\,|X|^2)$.

## Depends on

- [Quartets shared by two tripartitions](tripartition-shared-quartet-count.md)

## Proof depends on

- [Consistency of exact quartet-support maximization for the unrooted species tree](../../phylogenetics/quartet-support-and-determination-of-trees-by-qu/consistency-of-exact-quartet-support-maximizatio.md)

## Expansion

Rooting an unrooted binary tree with all bipartitions in $X$ on any edge gives a rooted tree whose root split $A' \mid L \setminus A'$ and whose non-root clusters all lie in $X'$; conversely every such rooted tree unroots to one. By induction on $|A|$, $V(A)$ is the maximum, over rooted binary trees on $A$ with all clusters in $X'$, of the sum of $w$ over their nodes, the tripartition of a node with cluster $B$ and children $B', B \setminus B'$ being $B' \mid B \setminus B' \mid L \setminus B$. Hence $V(L)$ is the largest sum of $w$ over the internal nodes of an admissible unrooted tree, which by the tripartition page is twice its weighted quartet score. The weighted quartet score is $k$ times the total quartet support with empirical frequencies, so the two have the same maximizers. Positive internal branch lengths make the species quartet the strict plurality on every four-taxon set (a star quartet would have none), and the consistency result then makes $S$ the unique unconstrained maximizer almost surely for large $k$. Each bipartition of $S$ occurs in a gene tree with positive probability at every locus, so almost surely all of them lie in $X_0^{(k)} \subseteq X^{(k)}$ for large $k$; the constrained search space then contains $S$, and every constrained maximizer is an unconstrained one. The recursion scores $O(|X|^2)$ admissible splits, each in $O(nk)$ time. ASTRAL-II enlarges $X$ beyond $X_0$ heuristically (greedy consensus resolutions and similarity-based additions) to guard against gene-tree estimation error.

## Sources

- S. Mirarab, T. Warnow, *ASTRAL-II: coalescent-based species tree estimation with many hundreds of taxa and thousands of genes*, Bioinformatics (2015). <https://doi.org/10.1093/bioinformatics/btv234> (PMCID: PMC4765870)
- S. Mirarab, R. Reaz, Md. S. Bayzid, T. Zimmermann, M. S. Swenson and T. Warnow, *ASTRAL: genome-scale coalescent-based species tree estimation*, Bioinformatics 30 (2014), i541–i548, <https://academic.oup.com/bioinformatics/article/30/17/i541/200803> (Section 2, the dynamic program).
