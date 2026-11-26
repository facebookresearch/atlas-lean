# Bayes–Nash equilibrium of the first-price auction with uniform values

In a first-price single-item auction with $n \ge 2$ bidders whose values are independent and uniform on $[0, 1]$, the symmetric strategy $\beta(v) = \frac{n-1}{n} v$ is a Bayes–Nash equilibrium, truthful bidding is not, and the expected revenue at this equilibrium is $\frac{n-1}{n+1}$, equal to the expected revenue of the second-price auction.

## Proof sketch

If the others bid $\beta$, their bids lie in $[0, \frac{n-1}{n}]$, so a bidder with value $v$ who bids $b \ge 0$ wins with probability $\min\!\big(1, \frac{nb}{n-1}\big)^{n-1}$ (ties have probability zero). A bid $b > \frac{n-1}{n}$ already wins with probability $1$, so it pays strictly more than the bid $\frac{n-1}{n}$ for the same win and gives strictly lower utility; it is never optimal. On $[0, \frac{n-1}{n}]$, maximizing $(v - b)\big(\frac{nb}{n-1}\big)^{n-1}$ gives $b = \frac{n-1}{n}v$. The revenue is the expected maximum bid, $\frac{n-1}{n} \cdot \frac{n}{n+1}$.

## Depends on

- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)
- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)

## Proof depends on

- [Revenue equivalence (in expectation)](../myerson-s-lemma-and-revenue-equivalence/set-integral-payment-eq.md)

## Sources

- Vijay Krishna, "Auction Theory", 2nd ed., Academic Press, 2010, Chapter 2 (Private Value Auctions: A First Look).
