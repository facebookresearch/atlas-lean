# Bayes–Nash equilibrium of the first-price auction with uniform values

In a first-price single-item auction with $n \ge 2$ bidders whose values are independent and uniform on $[0, 1]$, the symmetric strategy $\beta(v) = \frac{n-1}{n} v$ is a Bayes–Nash equilibrium, truthful bidding is not, and the expected revenue at this equilibrium is $\frac{n-1}{n+1}$, equal to the expected revenue of the second-price auction.

## Proof sketch

If others bid $\beta$, a bidder with value $v$ bidding $b$ wins with probability $(nb/(n-1))^{n-1}$, and maximizing $(v - b)$ times this probability gives $b = \frac{n-1}{n}v$. The revenue is the expected maximum bid, $\frac{n-1}{n} \cdot \frac{n}{n+1}$.

## Depends on

- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)
- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)

## Proof depends on

- [Revenue equivalence (in expectation)](../myerson-s-lemma-and-revenue-equivalence/set-integral-payment-eq.md)

## Sources

- Jason D. Hartline, "Mechanism Design and Approximation", Book manuscript, chapters 1–7 revised 20 September 2021, 2021.
