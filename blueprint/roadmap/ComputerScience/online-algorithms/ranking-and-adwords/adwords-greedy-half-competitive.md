# Greedy is 1/2-competitive for AdWords

In the truncated-spend model with capped bids $0 \le b_{tj} \le B_j$, the **Greedy** algorithm, which assigns each query to a bidder maximizing the effective payment $\min(b_{tj}, \text{remaining budget of } j)$, earns at least half the revenue of every offline assignment in the same model: for all pairwise disjoint sets $A_j$ of queries, its revenue is at least $\frac12 \sum_j \min\big(B_j, \sum_{t \in A_j} b_{tj}\big)$. No small-bid assumption is needed.

## Proof sketch

Fix an offline assignment and charge its loss bidder by bidder. If the offline assignment earns more than Greedy on a query $t \in A_j$, then when $t$ arrived bidder $j$ had at most Greedy's payment on $t$ left, so $j$'s final spend $S_j$ under Greedy is at least $B_j$ minus that payment. Summing, the loss on the queries in $A_j$ is at most $S_j$, so the offline revenue is at most twice Greedy's. The same accounting bounds Greedy against the fractional relaxation: with $g_t$ Greedy's payment on $t$, every pair satisfies $b_{tj} \le g_t + b_{tj} S_j / B_j$ (the bids are capped), and multiplying by a feasible $x_{tj}$ and summing gives $\sum_{t,j} b_{tj} x_{tj} \le 2 \cdot$ revenue.

## Depends on

- [The AdWords (online budgeted allocation) problem and its LP relaxation](adwords-problem-and-lp.md)

## Sources

- A. Mehta, A. Saberi, U. Vazirani and V. Vazirani, "AdWords and Generalized Online Matching", Journal of the ACM 54(5), 2007.
- S. Lahaie, D. M. Pennock, A. Saberi and R. V. Vohra, "Sponsored Search Auctions", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
- A. Mehta, "Online Matching and Ad Allocation", Foundations and Trends in Theoretical Computer Science 8(4), 2013, §5.2: the capped bid $\min\{bid_{uv}, B_u - S_u\}$ and Theorem 5.1 with its proof, pp. 308-309. <https://static.googleusercontent.com/media/research.google.com/en/us/pubs/archive/41870.pdf>
