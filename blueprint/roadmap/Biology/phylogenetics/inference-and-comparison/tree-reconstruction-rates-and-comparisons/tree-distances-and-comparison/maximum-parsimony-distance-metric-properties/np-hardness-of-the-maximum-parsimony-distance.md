# NP-hardness of computing the maximum parsimony distance

Let $T_1, T_2$ be phylogenetic trees on $X$ and $d_{MP}(T_1,T_2) = \max_f |l_f(T_1) - l_f(T_2)|$ their [maximum parsimony distance](maximum-parsimony-distance-is-a-metric-bounded-by-spr.md); let $d^i_{MP}$ be the same maximum restricted to characters with at most $i$ states.

**Theorem.**

1. Computing $d_{MP}(T_1,T_2)$ is NP-hard.
2. For every fixed $i \ge 2$, computing $d^i_{MP}(T_1,T_2)$ is NP-hard.
3. If one of the two trees is a star tree, $d_{MP}(T_1,T_2)$ can be computed in polynomial time.

Two facts used throughout: changing the state of one taxon changes a parsimony score by at most one; and from any optimal character with $l_f(T_1) < l_f(T_2)$ one can build, in polynomial time, an optimal character that is constant on every set of sibling leaves (children of a vertex all of whose children are leaves) of $T_1$.

So although $d_{MP}$ is a natural lower bound for the SPR distance, which is itself NP-hard, computing the lower bound is not easier in the worst case.

## Expansion

Hardness for two-state characters is shown by a reduction from Cubic Max Cut: the trees are built from the graph so that the parsimony difference of a binary character measures the number of edges cut by the corresponding vertex bipartition, and the monochromatic-sibling lemma lets one restrict to characters that respect the gadgets. Hardness for unrestricted characters is shown separately, by a reduction from Cubic Maximum Independent Set, in which an optimal character colours the vertices of a maximum independent set with the root state; neither hardness result implies the other. When one tree is a star, its parsimony score is $n$ minus the size of the largest state class, which makes the maximization tractable.

## Sources

- Mareike Fischer, Steven Kelk, "On the Maximum Parsimony distance between phylogenetic trees", arXiv (2014); Annals of Combinatorics (2016). Section 4 (Theorem 4.6, Corollary 4.7 and the supporting lemmas), Appendix. <https://doi.org/10.48550/arXiv.1402.1553>. Published version: Annals of Combinatorics 20(1) (2016), 87–113, <https://doi.org/10.1007/s00026-015-0298-1>; locators above refer to the arXiv version.
