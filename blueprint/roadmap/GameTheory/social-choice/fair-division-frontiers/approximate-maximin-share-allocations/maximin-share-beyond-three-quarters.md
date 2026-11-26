# Maximin share approximation beyond three quarters

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every instance a complete $\bigl(\tfrac34 + \tfrac{3}{3836}\bigr)$-MMS allocation exists. In contrast, approaches that normalize by the proportional share $v_i(M)/n$ in place of $\mu_i$ cannot certify any guarantee of the form $\tfrac34 + \Omega(1)$, since there are instances where some agent's best bag in such schemes is worth only $(\tfrac34 + o(1))\mu_i$.

## Proof sketch

Apply new reduction rules (including bundles of four goods and asymmetric pairs) that keep the instance ordered and normalized by $\mu_i$ instead of by the proportional share. The analysis splits agents according to how much value lies in large goods; for agents with many medium goods a refined bag-filling initialization with weighted counting gives a gain of a small absolute constant over $3/4$, computed to be $3/3836$.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)
- [Optimal maximin-share approximation](../../optimal-maximin-share-approximation.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)
- [Three-quarters maximin share allocations in polynomial time](three-quarters-mms-polynomial-time.md)

## Sources

- H. Akrami, J. Garg, "Breaking the 3/4 Barrier for Approximate Maximin Share", SODA 2024, arXiv:2307.07304.
