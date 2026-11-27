# Critical-bid mechanisms are truthful and coincide with Myerson payments

If a binary allocation rule is monotone in each bidder's bid, then its critical-bid mechanism is DSIC, individually rational and normalized, and the critical-bid payment equals Myerson's payment $b_i x_i(b) - \int_0^{b_i} x_i(z, b_{-i})\, dz$. Conversely an allocation rule with a threshold form is monotone.

## Proof sketch

A monotone binary allocation curve is a step function at the critical bid, so Myerson's integral evaluates to the critical bid for winners; truthfulness follows from Myerson's lemma or directly.

## Depends on

- [Critical bid of a binary monotone allocation rule](critical-bid-of-a-binary-monotone-allocation-rule.md)
- [Myerson's lemma](../myerson-s-lemma-and-revenue-equivalence/is-incentive-compatible-on-iff.md)

## Proof depends on

- [Payment formula](../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
- Roger B. Myerson, "Optimal Auction Design", Mathematics of Operations Research, 1981.
