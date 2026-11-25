# Existence of complete EFX allocations

Let $N$ be a finite nonempty set of $n \ge 1$ agents and $M$ a finite set of indivisible goods, and let each agent $i$ have an
additive valuation $v_i$ with $v_i(g) \ge 0$ for every good $g$. An allocation $(X_1, \dots, X_n)$ consists of pairwise disjoint, possibly empty bundles whose union is $M$ (every good is allocated). It is *envy-free up to any good* (EFX) if for all agents $i, j$ and every good
$g \in X_j$,

$$v_i(X_i) \ge v_i(X_j \setminus \{g\}).$$

This is the strong convention: the condition is required for every good in $X_j$, including goods that agent
$i$ values at zero. A weaker convention, used in some of the literature, quantifies only over goods $g$ with
$v_i(g) > 0$, and existence results under one convention do not automatically transfer to the other.

**Question posed by the cited sources.** Does every instance with additive valuations admit a complete EFX allocation?

**Status (as of the sources below).** Complete EFX allocations are known to exist for two agents and, by
Chaudhury, Garg and Mehlhorn, for three agents with additive valuations. For four or more agents these sources leave the general question unresolved. Alkassar, Fouz and Mehlhorn (2026) prove existence, in the strong sense above, for four
additive agents with at most nine goods; this is progress on the four-agent case, not a solution.

## Expansion

A good expansion separates:

1. Finite nonempty agent sets, finite goods, nonnegative additive valuations, complete allocations with
    possibly empty bundles, and the strong all-goods EFX predicate, distinct from the positive-goods-only
    convention.
2. The cited two-agent and three-agent existence results and the four-agent, at-most-nine-goods result,
    each with its precise valuation, completeness and zero-good conventions.
3. The unrestricted existence question as a research node. A counterexample would need an exact valuation
    instance and exclusion of every complete allocation, not merely failure of a particular algorithm.

This page records the cited results and question, not a certification of the question's present status.

## Sources

- B. R. Chaudhury, J. Garg and K. Mehlhorn, *EFX exists for three agents*, EC 2020; arXiv:2002.05119, abstract. <https://arxiv.org/abs/2002.05119>
- E. Alkassar, M. Fouz and K. Mehlhorn, *Complete EFX allocations exist for four additive agents and up to nine goods*, arXiv:2608.08590, abstract. <https://arxiv.org/abs/2608.08590>
