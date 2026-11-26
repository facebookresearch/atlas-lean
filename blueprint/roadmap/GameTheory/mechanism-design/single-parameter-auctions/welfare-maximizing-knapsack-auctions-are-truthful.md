# Welfare-maximizing knapsack auctions are truthful

In a knapsack auction, bidder $i$ has public size $w_i$ and private value, and feasible allocations are $0$-$1$ vectors $x$ with $\sum_i w_i x_i \le W$. Every welfare-maximizing allocation rule over this feasible set is monotone, so the mechanism charging critical bids is DSIC and individually rational, and its payments are Myerson payments. A welfare-maximizing rule exists for nonnegative bids.

## Proof sketch

Raising a winner's bid increases the welfare of every allocation containing it by the same amount, so a welfare maximizer that included $i$ still includes $i$.

## Depends on

- [Critical bid of a binary monotone allocation rule](critical-bid-of-a-binary-monotone-allocation-rule.md)

## Proof depends on

- [Critical-bid mechanisms are truthful and coincide with Myerson payments](critical-bid-mechanisms-are-truthful-and-coincide-with-myerson-payments.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
