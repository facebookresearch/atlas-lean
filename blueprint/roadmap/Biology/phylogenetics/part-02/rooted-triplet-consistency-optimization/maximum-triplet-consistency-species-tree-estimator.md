# Maximum triplet consistency species tree estimator

**Problem.** Given rooted binary gene trees $\mathcal G = \{g_1, \dots, g_k\}$ on taxon set $X$ with $|X| = n$, let $w_{\mathcal G}(t)$ be the number of gene trees agreeing with rooted triplet $t$. The **maximum triplet consistency (CTC)** problem seeks a rooted binary species tree $T$ maximizing $\sum_{r} w_{\mathcal G}(T|_r)$ over all three-taxon subsets $r$, i.e. the total number of (gene tree, triplet) agreements. In the constrained version, only species trees whose every subtree-bipartition occurs in some gene tree are searched.

**Counting lemmas.** Each internal node of a rooted binary tree defines a subtree-bipartition $x = (X_1 | X_2)$ of the taxa below it, and every triplet maps to the unique node at which it splits two-versus-one.

1. With $|X_1| = n_1$, $|X_2| = n_2$, the number of triplets mapped to $x$ is

    $$N_T(n_1, n_2) = \binom{n_1}{2} n_2 + \binom{n_2}{2} n_1 = \frac{n_1 n_2 (n_1 + n_2 - 2)}{2}.$$

2. For subtree-bipartitions $x = (X_1|X_2)$ and $y = (Y_1|Y_2)$, the number of triplets mapped to both is

    $$\mathcal M(x, y) = N_T(|X_1\cap Y_1|, |X_2 \cap Y_2|) + N_T(|X_1 \cap Y_2|, |X_2 \cap Y_1|).$$

The triplet consistency score of $x$ is $TC_{\mathcal G}(x) = \sum_y \mathcal M(x,y)$ over all subtree-bipartitions $y$ of the gene trees, computable in $O(n^2 k)$ time.

**Dynamic program.** For a cluster $A$, $V(A) = 0$ if $|A| = 1$ and otherwise

$$V(A) = \max_{(A'|A\setminus A') \in \mathcal{SBP}} \big\{V(A') + V(A \setminus A') + TC_{\mathcal G}(A'|A\setminus A')\big\},$$

and $V(X)$ is the optimum; the total running time is $O(n^2 k\,|\mathcal{SBP}|^2)$ for an allowed set $\mathcal{SBP}$ of subtree-bipartitions.

**Theorem (statistical consistency).** If the gene trees are true gene trees evolving independently within a species tree under the multispecies coalescent, then both the exact and the constrained CTC solutions converge in probability to the true species tree topology as $k \to \infty$.

## Depends on

- [The multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)
- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)

## Expansion

A rooted three-taxon species tree has no anomaly zone: under the multispecies coalescent, the gene-tree triplet matching the species tree has probability $1 - \tfrac23 e^{-\tau}$, larger than each alternative's $\tfrac13 e^{-\tau}$ for internal branch length $\tau > 0$ in coalescent units. So for every triplet the species-tree resolution wins the majority with probability tending to one, the true tree maximizes every summand at once, and any other tree loses on at least one triplet. The two-term formula for $\mathcal M$ counts each shared triplet once, because a triplet $ab|c$ mapped to both bipartitions has $a, b$ in one intersection block and $c$ in the opposite one. The construction mirrors quartet-based estimators but uses rooted triplets, whose majority is consistent for rooted gene trees.

## Sources

- M. Islam, K. Sarker, T. Das, R. Reaz, M. S. Bayzid, "STELAR: a statistically consistent coalescent-based species tree estimation method by maximizing triplet consistency", BMC Genomics 21:136 (2020), Lemmas 1–3 (Eqs 1–3), Theorems 1–2 and the dynamic programming recursion, <https://doi.org/10.1186/s12864-020-6519-y>, PMCID PMC7011378.
