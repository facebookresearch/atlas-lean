# Profit extraction for digital goods

For a target profit $R \ge 0$ and a set $s$ of bidders, the mechanism ProfitExtract$_R$ finds the largest $k$ such that the $k$ highest bids in $s$ are each at least $R/k$, sells to those $k$ bidders at price $R/k$, and sells to nobody if no such $k$ exists. It is DSIC, individually rational and normalized; its profit is exactly $R$ if $R \le \mathcal F(b_s)$ and $0$ otherwise.

## Proof sketch

The allocation is monotone with threshold structure, and each winner's critical bid is $R/k$. If $\mathcal F(b_s) \ge R$ then some $k$ bids are at least $R/k$, and the largest such $k$ is selected.

## Depends on

- [Digital goods auction and single-price benchmarks](digital-goods-auction-and-single-price-benchmarks.md)

## Proof depends on

- [Critical-bid mechanisms are truthful and coincide with Myerson payments](../single-parameter-auctions/critical-bid-mechanisms-are-truthful-and-coincide-with-myerson-payments.md)

## Sources

- Jason D. Hartline and Anna R. Karlin, "Profit Maximization in Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
