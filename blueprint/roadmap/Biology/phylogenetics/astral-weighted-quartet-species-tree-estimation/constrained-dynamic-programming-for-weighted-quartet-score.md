# Constrained dynamic programming for the weighted quartet score

Let $\mathcal G$ be a set of $k$ binary gene trees on a set $L$ of $n$ taxa and let $w$ be the tripartition weight. Fix a set $X$ of bipartitions of $L$ and let $X' = \{A : A \mid L \setminus A \in X\}$ be the set of all their sides. ASTRAL maximizes the weighted quartet score over species trees all of whose bipartitions lie in $X$ by the recursion

$$V(A) = \max_{A' \subset A \,:\, A' \in X',\ A \setminus A' \in X'} \Big\{ V(A') + V(A \setminus A') + w\big(A' \mid A \setminus A' \mid L \setminus A\big) \Big\},$$

where $V(A)$ is the optimal score of a subtree on the cluster $A$ and singletons have $V = 0$. The optimal tree is recovered by backtracking from the root cluster.

**Theorem 1 (consistency).** Let $X_0$ be the set of bipartitions found in the input gene trees. If $X_0 \subseteq X$, then ASTRAL run with the set $X$ is statistically consistent under the multispecies coalescent model: as the number of independent true gene trees grows, the probability that it returns the true unrooted species-tree topology tends to one.

**Theorem 2 (running time).** The running time of ASTRAL-II is $O(nk\,|X|^2)$.

## Depends on

- [Quartets shared by two tripartitions](tripartition-shared-quartet-count.md)
- [Consistency of exact quartet-support maximization for the unrooted species tree](../../phylogenetics/quartet-support-and-determination-of-trees-by-qu/consistency-of-exact-quartet-support-maximizatio.md)

## Expansion

Under the multispecies coalescent the species quartet is the most probable gene-tree quartet for every four taxa, so with enough genes the species tree is the unique maximizer of quartet support. Every bipartition of the species tree eventually occurs in some gene tree, hence in $X_0 \subseteq X$, so the constrained search space contains the unconstrained optimum. The recursion scores $O(|X|^2)$ admissible splits, each in $O(nk)$ time. ASTRAL-II enlarges $X$ beyond $X_0$ heuristically (greedy consensus resolutions and similarity-based additions) to guard against gene-tree estimation error.

## Sources

- S. Mirarab, T. Warnow, *ASTRAL-II: coalescent-based species tree estimation with many hundreds of taxa and thousands of genes*, Bioinformatics (2015). <https://doi.org/10.1093/bioinformatics/btv234> (PMCID: PMC4765870)
