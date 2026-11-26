# Fair Proportion equals Equal Splits exactly on semi-balanced trees

**Setting.** Use the Fair Proportion index $FP_T$ and the Equal Splits index $ES_T$ on a rooted binary phylogenetic tree $T$ with leaf set $[n]$, as in [Extremal gaps between the Fair Proportion and Equal Splits indices](extremal-gaps-between-the-fair-proportion-and-equal-splits-indices.md). The *fully balanced tree of height $h$*, $T^{fb}_h$, is the binary tree with $2^h$ leaves all at depth $h$. A *semi-balanced tree* is a rooted binary tree whose two maximal pending subtrees are fully balanced, $T=(T^{fb}_{h'},T^{fb}_{h''})$, with possibly different heights $h'$ and $h''$.

**Theorem.** $FP_T(i)=ES_T(i)$ for every leaf $i\in[n]$ and every assignment of positive edge lengths if and only if $T$ is semi-balanced.

In addition, on rooted trees the Fair Proportion index coincides with the Shapley value of the phylogenetic diversity game, which is the unique value satisfying Shapley's efficiency, symmetry, null-player and additivity axioms on this class of games; Equal Splits does not, so on non-semi-balanced trees Equal Splits is not a Shapley value.

## Expansion

Since both indices are linear in edge lengths, equality for all lengths means equality of the coefficients edge by edge: for every leaf $i$ and every edge $e$ on its root path, $n(e)=\Pi(e,i)=2^{m(e,i)}$, where $m(e,i)$ is the number of edges between $e$ and $i$. Below every non-root edge this forces the subtree to have $2^{m}$ leaves for every leaf at distance $m$, which forces it to be fully balanced. The two edges at the root are not constrained relative to each other, since each is shared only within its own side, so the two root subtrees may have different heights. Conversely, in a fully balanced subtree each edge at height $j$ above the leaves has exactly $2^j$ descendants, which is the Equal Splits divisor.

## Depends on

- [Extremal gaps between the Fair Proportion and Equal Splits indices](extremal-gaps-between-the-fair-proportion-and-equal-splits-indices.md)

## Sources

- Kristina Wicke, Mike Steel, "Combinatorial properties of phylogenetic diversity indices", arXiv:1902.02463 (2019): Section 3 (fully balanced and semi-balanced trees, characterization theorem), Section 4 (uniqueness of the Shapley value for phylogenetic tree games and its equality with Fair Proportion). <https://doi.org/10.48550/arXiv.1902.02463> Published version: Journal of Mathematical Biology 80 (2019) 687–715, <https://doi.org/10.1007/s00285-019-01438-0>.
