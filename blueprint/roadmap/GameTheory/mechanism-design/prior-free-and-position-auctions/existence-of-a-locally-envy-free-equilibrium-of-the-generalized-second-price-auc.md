# Existence of a locally envy-free equilibrium of the generalized second-price auction

In the full-information generalized second-price auction, where bidders are ranked by bid and each pays per click the next-lower bid (or the highest unassigned bid for the last slot), with nonnegative values and at least $k$ bidders there is a bid profile that is a pure Nash equilibrium robust to all tie-breaking, whose outcome is the optimal assignment at the minimal locally envy-free prices. These prices coincide with the VCG (Clarke-pivot) payments of the position auction.

## Proof sketch

Let each bidder in slot $s+1$ bid the minimal envy-free price of slot $s$; then each slot pays its envy-free price, local envy-freeness rules out profitable moves to adjacent slots, and envy-freeness propagates to non-adjacent slots by sortedness. The VCG externality of slot $s$ telescopes to the same recursion.

## Depends on

- [Position auction and locally envy-free assignment](position-auction-and-locally-envy-free-assignment.md)
- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Proof depends on

- [Position assignments are optimal iff supported by locally envy-free prices](position-assignments-are-optimal-iff-supported-by-locally-envy-free-prices.md)

## Sources

- Sebastien Lahaie, David M. Pennock, Amin Saberi and Rakesh V. Vohra, "Sponsored Search Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
