# Simple mechanisms are constant-factor optimal for a subadditive buyer over independent items

For a single buyer whose valuation is subadditive over independent items, i.e. $v(S) = V(\{x_j\}_{j \in S})$ with independent item types $x_j$ and $V$ monotone subadditive in the set of items, the better of selling separately and grand bundling achieves a constant fraction of the optimal revenue.

## Proof sketch

Generalize the core-tail decomposition: subadditivity allows splitting the value of the core and the tail, and independence across items gives concentration of the core value via Talagrand-type inequalities for subadditive functions of independent variables. The tail is again handled by selling items separately, and grand bundling extracts the concentrated core value.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Core-tail decomposition of the optimal revenue](core-tail-decomposition-revenue.md)
- [The better of selling separately and grand bundling is a 6-approximation](max-srev-brev-six-approximation.md)

## Sources

- A. Rubinstein, S. M. Weinberg, "Simple Mechanisms for a Subadditive Buyer and Applications to Revenue Monotonicity", EC 2015; ACM Transactions on Economics and Computation 6(3-4) (2018).
