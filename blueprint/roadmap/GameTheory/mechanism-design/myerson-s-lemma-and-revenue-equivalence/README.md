# Myerson's lemma and revenue equivalence

An agent with a value $t \in [a, b]$ who reports $s$ to a single-parameter mechanism receives the quantity $Q(s)$ (an allocation probability) and pays $P(s)$, for a utility $t\,Q(s) - P(s)$. Myerson's lemma (Myerson 1981, Lemma 2) characterizes incentive compatibility: truthful reporting is optimal for every value if and only if $Q$ is monotone and the truthful utility $U$ satisfies the envelope formula $U(t) = U(a) + \int_a^t Q$. No continuity of $Q$ is needed. The payments are therefore determined by the allocation rule and the payment of the lowest type, $P(t) = t\,Q(t) - \int_a^t Q - U(a)$, so two incentive-compatible mechanisms with the same allocation rule and the same payment at the lowest type raise the same expected revenue under every distribution of values (the revenue-equivalence theorem, Myerson 1981, Corollary). The results apply to the interim form of a Bayesian mechanism and, with the other bids fixed, to dominant-strategy mechanisms (Nisan 2007, Theorem 9.39; Hartline and Karlin 2007, Theorem 13.6).

- [Truthful utility](truthful-utility.md)
- [Incentive compatibility on an interval](is-incentive-compatible-on.md)
- [Myerson's inequality (4.6)](is-incentive-compatible-on-iff-utility.md)
- [Myerson's inequality, applied](utility-add-mul-le-utility.md)
- [Monotonicity of incentive-compatible allocations](allocation-monotone-on.md)
- [Two-sided comparison lemma](eq-of-abs-sub-le-mul.md)
- [Envelope formula](envelope-formula.md)
- [Myerson's lemma](is-incentive-compatible-on-iff.md)
- [Payment formula](payment-formula.md)
- [Revenue equivalence (pointwise)](payment-eq-on-of-is-incentive-compatible.md)
- [Revenue equivalence (in expectation)](set-integral-payment-eq.md)
- [Individual rationality from the lowest type](utility-nonneg-of-lowest.md)
- [Myerson's Lemma 2 for one bidder](is-incentive-compatible-on-and-utility-n.md)
- [Single-parameter quasilinear mechanisms: model, DSIC and IR](remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)

## Dominant-strategy auctions

- [Dominant-strategy incentive compatibility of a single-parameter auction](dsic.md)
- [Allocations of a dominant-strategy incentive-compatible auction are monotone](myerson-monotone.md)
- [Myerson payment of an allocation rule](myerson-payment.md)
- [The Myerson payment makes truthful bidding optimal](myerson-payment-dsic.md)
- [The Myerson payment of a zero bid is zero](myerson-payment-zero.md)

## Related topics

- [Revelation principle](../revelation-principle/README.md): why direct, incentive-compatible mechanisms suffice.
- [Optimal auctions and virtual valuations](../optimal-auctions-and-virtual-valuations/README.md): the payment formula integrated against the value distribution.
- [Myerson–Satterthwaite theorem](../myerson-satterthwaite.md): the envelope formula applied to both sides of a bilateral trade.
