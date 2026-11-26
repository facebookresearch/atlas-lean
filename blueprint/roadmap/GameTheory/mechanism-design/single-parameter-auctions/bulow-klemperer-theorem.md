# Bulow–Klemperer theorem

For a single item and bidders with i.i.d. values drawn from a regular distribution with a density on $[0, h]$, the expected revenue of the second-price auction with no reserve and $n + 1$ bidders is at least the expected revenue of Myerson's optimal auction with $n$ bidders, and hence at least that of every DSIC, individually rational single-item mechanism with $n$ bidders (and of every Bayes–Nash equilibrium with nonpositive zero-type payments).

## Proof sketch

The expected virtual value of a single bidder is zero. The second-price auction with $n+1$ bidders maximizes virtual welfare among rules that always allocate; the rule that runs Myerson's auction on $n$ bidders and otherwise gives the item to bidder $n+1$ always allocates and has the same virtual welfare as Myerson's auction, since the extra bidder contributes zero in expectation.

## Depends on

- [Optimal auctions for regular distributions](../optimal-auctions-and-virtual-valuations/remaining-clauses-of-optimal-auctions-for-regular-distributi.md)
- [Virtual valuation](../optimal-auctions-and-virtual-valuations/virtual-value.md)
- [Vickrey's theorem](../vickrey-clarke-groves-mechanisms/second-price-truthful.md)

## Proof depends on

- [Myerson's revenue identity (4.10)](../optimal-auctions-and-virtual-valuations/integral-payment-mul-density.md)
- [Virtual surplus maximization is monotone](../optimal-auctions-and-virtual-valuations/virtual-surplus-maximization-is-monotone.md)

## Sources

- Jeremy Bulow and Paul Klemperer, "Auctions Versus Negotiations", The American Economic Review, 1996.
- Tim Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Cambridge University Press, 2016.
- Jason D. Hartline, "Mechanism Design and Approximation", Book manuscript, chapters 1–7 revised 20 September 2021.
