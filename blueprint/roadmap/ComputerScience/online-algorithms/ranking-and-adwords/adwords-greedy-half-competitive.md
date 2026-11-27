# Greedy is 1/2-competitive for AdWords

In the truncated-spend model with capped bids $0 \le b_{tj} \le B_j$, the **Greedy** algorithm, which assigns each query to a bidder maximizing the effective payment, earns revenue at least $\frac12 \sum_{t,j} b_{tj} x_{tj}$ for every feasible solution $x$ of the fractional relaxation; no small-bid assumption is needed.

## Proof sketch

Charge each unit of LP value either to a query on which Greedy earned at least as much, or to a bidder whose budget Greedy exhausted.

## Depends on

- [The AdWords (online budgeted allocation) problem and its LP relaxation](adwords-problem-and-lp.md)

## Sources

- A. Mehta, A. Saberi, U. Vazirani and V. Vazirani, "AdWords and Generalized Online Matching", Journal of the ACM 54(5), 2007.
- S. Lahaie, D. M. Pennock, A. Saberi and R. V. Vohra, "Sponsored Search Auctions", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
