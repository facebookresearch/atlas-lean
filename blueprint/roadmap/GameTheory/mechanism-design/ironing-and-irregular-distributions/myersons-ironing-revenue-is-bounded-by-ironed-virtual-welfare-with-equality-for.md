# Myerson's ironing: revenue is bounded by ironed virtual welfare, with equality for the ironed auction

For independent bidders with densities and ironed virtual valuations $\bar\varphi_i$, the expected revenue of every DSIC, individually rational mechanism is at most its expected ironed virtual welfare $\mathbb{E}[\sum_i \bar\varphi_i(v_i) x_i(v)]$, with equality when the allocation is constant on ironing intervals. The allocation rule maximizing ironed virtual welfare pointwise (allocating to the highest nonnegative ironed virtual value, ties broken consistently) is monotone, and with Myerson payments it is a revenue-optimal auction even for irregular distributions. For a single bidder this is the monopoly price; with samples the empirical Myerson auction uses the empirical revenue curve.

## Proof sketch

Integrating by parts, $\mathbb{E}[\varphi(v) x(v)] = \mathbb{E}[\bar\varphi(v) x(v)] - \int (\text{tail slack})\, dx$; monotonicity of $x$ makes the correction nonpositive, and it vanishes when $x$ is flat where the slack is positive.

## Depends on

- [Ironed virtual valuation](ironed-virtual-valuation.md)
- [Optimal auctions for regular distributions](../optimal-auctions-and-virtual-valuations/remaining-clauses-of-optimal-auctions-for-regular-distributi.md)

## Proof depends on

- [Myerson's revenue identity (4.10)](../optimal-auctions-and-virtual-valuations/integral-payment-mul-density.md)
- [Myerson's lemma](../myerson-s-lemma-and-revenue-equivalence/is-incentive-compatible-on-iff.md)

## Sources

- Roger B. Myerson, "Optimal Auction Design", Mathematics of Operations Research, 1981.
- Jason D. Hartline and Anna R. Karlin, "Profit Maximization in Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
