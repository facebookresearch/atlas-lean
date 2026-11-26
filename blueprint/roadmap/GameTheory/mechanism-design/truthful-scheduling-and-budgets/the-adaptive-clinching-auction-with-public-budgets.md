# The adaptive clinching auction with public budgets

With public budgets, the adaptive clinching auction raises a price clock and lets each bidder clinch units at the current price whenever the remaining supply exceeds the total demand of the other active bidders (demand at price $p$ being remaining budget over $p$ for active bidders). It is feasible, budget feasible, individually rational, Pareto optimal and DSIC with respect to values. Misreporting budgets can be profitable, so it is not truthful when budgets are private.

## Proof sketch

Each bidder clinches only units that the others cannot absorb, so its price path is independent of its own report until it drops out, which yields truthfulness in values. At the end supply is exhausted or every remaining bidder has exhausted its budget, which gives Pareto optimality.

## Depends on

- [Multi-unit auction with hard budgets](multi-unit-auction-with-hard-budgets.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Dobzinski–Lavi–Nisan impossibility for private budgets](dobzinski-lavi-nisan-impossibility-for-private-budgets.md)

## Sources

- Shahar Dobzinski, Ron Lavi and Noam Nisan, "Multi-unit auctions with budget limits", Games and Economic Behavior, 2012.
- Lawrence M. Ausubel, "An Efficient Ascending-Bid Auction for Multiple Objects", American Economic Review, 2004.
