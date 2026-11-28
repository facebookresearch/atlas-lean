# The maximin share is at most the proportional share

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every agent $i$, $\mu_i \le v_i(M)/n$. Moreover the maximin share is scale-invariant: replacing $v_i$ by $\lambda v_i$ for $\lambda > 0$ multiplies $\mu_i$ by $\lambda$, so an instance can be normalized so that $\mu_i = 1$ (or $v_i(M) = n$) for every agent with positive maximin share.

## Proof sketch

In any partition the smallest bundle is worth at most the average $v_i(M)/n$. Scale invariance is immediate from additivity.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Sources

- D. Kurokawa, A. D. Procaccia, J. Wang, "Fair Enough: Guaranteeing Approximate Maximin Shares", Journal of the ACM 65(2) (2018); EC 2016.
- J. Garg, S. Taki, "An Improved Approximation Algorithm for Maximin Shares", EC 2020; Artificial Intelligence 300 (2021), arXiv:1903.00029, Lemmas 2.3 and 2.4.
