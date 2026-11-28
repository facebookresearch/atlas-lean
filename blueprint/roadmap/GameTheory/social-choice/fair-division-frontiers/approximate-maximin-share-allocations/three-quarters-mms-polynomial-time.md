# Three-quarters maximin share allocations in polynomial time

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every instance a complete $\bigl(\tfrac34 + \tfrac{1}{12n}\bigr)$-MMS allocation exists, and a complete $\tfrac34$-MMS allocation can be computed in polynomial time.

## Proof sketch

Normalize so that $v_i(M) = n$ (which gives $\mu_i \le 1$), and apply the valid reductions for single goods, pairs $\{g_n, g_{n+1}\}$ and triples $\{g_{2n-1}, g_{2n}, g_{2n+1}\}$ while some agent values them at least $3/4$ (the pair $\{g_1, g_{2n+1}\}$ is also used, where it is a valid reduction). In the reduced instance every good after the first $2n$ is worth less than $1/4$ to every agent and every pair $\{g_n, g_{n+1}\}$ less than $3/4$; initialize $n$ bags with $\{g_k, g_{2n+1-k}\}$ and fill them greedily with small goods. A counting argument shows every agent eventually takes a bag worth at least $3/4$.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)
- [The maximin share is at most the proportional share](maximin-share-at-most-proportional-share.md)

## Sources

- M. Ghodsi, M. HajiAghayi, M. Seddighin, S. Seddighin, H. Yami, "Fair Allocation of Indivisible Goods: Improvements and Generalizations", EC 2018, arXiv:1704.00222.
- J. Garg, S. Taki, "An Improved Approximation Algorithm for Maximin Shares", EC 2020; Artificial Intelligence 300 (2021), arXiv:1903.00029.
