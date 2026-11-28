# Constant-factor comparison of fractional and integral expectation thresholds

For a nonempty proper increasing family $F$ of subsets of a finite nonempty set $X$, define $q(F)$ as the supremum of $p\in[0,1]$ for which some $G\subseteq2^X$ covers $F$ by containment and has $\sum_{S\in G}p^{|S|}\le1/2$. Such a cover means each $H\in F$ contains some $S\in G$. Define $q_f(F)$ with a weight $g(S)\in[0,1]$ for each $S\subseteq X$, requiring $\sum_{S\subseteq H}g(S)\ge1$ for each $H\in F$ and $\sum_{S\subseteq X}g(S)p^{|S|}\le1/2$. The empty subset is allowed in both. Then $q_f(F)\le(25\cdot512^4)q(F)$.

## Depends on

- [Fractional threshold (nonnegative weight version)](q-f.md)
- Integral cover threshold and a clipping bridge between nonnegative weights and weights at most one.

## Expansion

Separate fractional-to-integral rounding on a finite ground set at the literal density ratio: a feasible fractional containment cover at p supplies an integral cover at p/(25·512⁴) with the same budget. Carry the clipping, all-subset support and empty-witness conventions explicitly. The subsequent supremum comparison is the application.

## Proof outline

Prove the clipping/equivalence lemma on finite sets, then a cover-rounding theorem with the given factor, then the threshold comparison. Do not substitute the separate upper bound on the probabilistic threshold $p_c$.

## Sources

- [Comparator statement: `OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TalagrandExpectationThreshold.lean#L52-L57)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/175.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ExpectationThreshold/Main.lean)
