# Random sampling profit extraction is exactly 4-competitive

Random Sampling Profit Extraction partitions the bidders into two sets by independent fair coin flips, computes the optimal single-price profit of each part, and runs profit extraction on each part with the other part's benchmark as target. It is universally truthful (hence truthful in expectation) and individually rational, and its expected profit is at least $\mathcal F^{(2)}(b)/4$ for every bid vector; the constant $4$ is the least possible for this mechanism, attained in the limit by a two-bidder instance.

## Proof sketch

The profit is $\min(\mathcal F(b_{s}), \mathcal F(b_{\bar s}))$. A balls-in-bins argument over the winners of $\mathcal F^{(2)}$ shows the smaller part captures, in expectation, at least a quarter of the benchmark.

## Depends on

- [Digital goods auction and single-price benchmarks](digital-goods-auction-and-single-price-benchmarks.md)
- [Universally truthful and truthful-in-expectation randomized mechanisms](../dsic-characterizations/universally-truthful-and-truthful-in-expectation-randomized-mechanisms.md)

## Proof depends on

- [Profit extraction for digital goods](profit-extraction-for-digital-goods.md)
- [Universal truthfulness implies truthfulness in expectation, but not conversely](../dsic-characterizations/universal-truthfulness-implies-truthfulness-in-expectation-but-not-conversely.md)

## Sources

- Jason D. Hartline and Anna R. Karlin, "Profit Maximization in Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
