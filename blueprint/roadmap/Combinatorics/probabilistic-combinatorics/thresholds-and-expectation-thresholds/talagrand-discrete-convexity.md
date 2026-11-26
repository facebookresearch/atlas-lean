# Talagrand discrete convexity at the original density

Let $N\ge1$, $0<p<1$, $k=2^{75}$ and $D\subseteq 2^{[N]}$ with Bernoulli-$p$ measure $\sum_{S\in D}p^{|S|}(1-p)^{N-|S|}\ge1-1/k$. Let $A$ consist of every subset contained in no union of a $k$-tuple from $D$ (repetition allowed). There is a family of distinct generators $G$ such that every $S\in A$ contains some $I\in G$, and $\sum_{I\in G}p^{|I|}\le1/2$. No monotonicity is required of $D$.

## Depends on

- Finite Bernoulli product measure, containment cover, and the exceptional family for unions of exactly k entries.

## Proof outline

Separate the probability hypothesis from the exceptional containment construction. Keep $2^{75}$, repetitions and cost at the original density; an estimate at a rescaled density is not this assertion.

- Cover construction for the exceptional family with uniform measure-to-cost estimate at the same p.

## Sources

- [Comparator statement: `OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TalagrandDiscreteConvexity.lean#L46-L52)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/175.md)
