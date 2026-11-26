# Weighted Groves mechanisms are dominant-strategy incentive compatible

For strictly positive weights $w_i > 0$, every weighted Groves mechanism for an affine maximizer is DSIC on the unrestricted domain, for any tie-breaking in the maximization. With nonnegative weights the same holds provided every weight-zero agent is a dummy whose report does not affect the outcome and is charged a payment independent of its report; adverse tie-breaking at weight zero can otherwise break incentive compatibility.

## Proof sketch

Agent $i$'s utility under truthful reporting is $\frac{1}{w_i}$ times the affine objective at the chosen outcome minus a term independent of its report, so truth-telling maximizes it, exactly as in the Groves argument.

## Depends on

- [Affine maximizer and weighted Groves mechanism](affine-maximizer-and-weighted-groves-mechanism.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
