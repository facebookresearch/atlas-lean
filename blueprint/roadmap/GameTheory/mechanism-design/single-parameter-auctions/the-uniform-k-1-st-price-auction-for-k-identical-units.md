# The uniform (k+1)-st price auction for k identical units

In a multi-unit auction of $k$ identical items to unit-demand bidders, awarding items to the $k$ highest bids (ties broken by index) maximizes reported welfare, and charging every winner the $(k+1)$-st highest bid (or $0$ when there are at most $k$ bidders) is DSIC, individually rational and normalized; these payments are the critical bids and coincide with the VCG payments. For $k = 1$ this is the Vickrey auction. Charging winners discriminatory prices based on the next-lower bid is not DSIC in general.

## Proof sketch

A winner's critical bid is the $k$-th highest of the others' bids ($0$ if there are fewer than $k$ others), which is the $(k+1)$-st highest bid overall; the externality of a winner on the others is exactly displacing the $(k+1)$-st bidder.

## Depends on

- [Critical bid of a binary monotone allocation rule](critical-bid-of-a-binary-monotone-allocation-rule.md)
- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Proof depends on

- [Critical-bid mechanisms are truthful and coincide with Myerson payments](critical-bid-mechanisms-are-truthful-and-coincide-with-myerson-payments.md)
- [Vickrey's theorem](../vickrey-clarke-groves-mechanisms/second-price-truthful.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- William Vickrey, "Counterspeculation, Auctions, and Competitive Sealed Tenders", The Journal of Finance, 1961.
