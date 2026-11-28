# Valid reduction rules preserving maximin shares of the remaining agents

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. In an ordered normalized instance with $\mu_i = 1$ for all $i$ and goods $g_1 \ge g_2 \ge \dots$ (common order), the following steps (each applicable when the goods it names exist, that is, $m \ge 1$, $m \ge n + 1$ and $m \ge 2n + 1$ respectively) remove one agent and some goods without decreasing the maximin share of any remaining agent (with respect to $n - 1$ bundles): giving the single good $\{g_1\}$ to some agent; giving $\{g_n, g_{n+1}\}$ to some agent; giving $\{g_{2n-1}, g_{2n}, g_{2n+1}\}$ to some agent. Hence if some agent values one of these bundles at least $\alpha$, assigning it to her is a valid reduction for $\alpha$-MMS.

## Proof sketch

Fix a remaining agent $j$ and an optimal $n$-partition for $j$. For $\{g_1\}$: remove the part containing $g_1$ and redistribute its other goods, obtaining $n - 1$ parts each worth at least $1$. For $\{g_n, g_{n+1}\}$: by pigeonhole two of $g_1, \dots, g_{n+1}$ lie in one part, and swapping them with $g_n, g_{n+1}$ (which are no more valuable) before deleting that part leaves $n - 1$ parts of value at least $1$. The triple rule is analogous with $2n + 1$ goods.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Proof depends on

- [Reduction to ordered instances for maximin share approximation](ordered-instance-reduction-mms.md)
- [The maximin share is at most the proportional share](maximin-share-at-most-proportional-share.md)

## Sources

- J. Garg, S. Taki, "An Improved Approximation Algorithm for Maximin Shares", EC 2020; Artificial Intelligence 300 (2021), arXiv:1903.00029.
- M. Ghodsi, M. HajiAghayi, M. Seddighin, S. Seddighin, H. Yami, "Fair Allocation of Indivisible Goods: Improvements and Generalizations", EC 2018, arXiv:1704.00222.
