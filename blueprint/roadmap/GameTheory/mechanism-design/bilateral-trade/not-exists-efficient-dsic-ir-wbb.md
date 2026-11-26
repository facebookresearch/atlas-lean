# Dominant-strategy bilateral-trade impossibility

No deterministic bilateral-trade
mechanism on `[0, 1]` types is simultaneously ex-post efficient, DSIC for both sides, ex-post
individually rational, and weakly budget-balanced. At an interior profile `0 < s < b < 1`
efficiency forces trade; efficiency, buyer DSIC and ex-post IR force the buyer to pay `s`
(`payBuyer_eq_of_lt`), and efficiency, seller DSIC and ex-post IR force the seller to receive
`b` (`paySeller_eq_of_lt`). The seller would then receive `b - s > 0` more than the buyer pays,
which weak budget balance forbids.

The mechanism is deterministic (`alloc s b ∈ {0, 1}`) and has zero transfers off trade by
construction: both utilities are `0` when `alloc s b = 0`. So this is neither the Bayesian
Myerson–Satterthwaite impossibility nor a statement about mechanisms that randomize trade or
make payments without trade.

## Sources

- K. Goldner, DS 574 Algorithmic Mechanism Design, Lecture 15 (Fall 2025), Definition 2, the utilities after it, conditions (1)–(3) and Theorem 1.
