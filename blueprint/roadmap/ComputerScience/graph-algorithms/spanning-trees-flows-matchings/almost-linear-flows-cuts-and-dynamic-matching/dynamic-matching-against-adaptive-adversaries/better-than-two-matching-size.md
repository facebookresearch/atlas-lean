# Better-than-2 approximate matching size in polylogarithmic worst-case update time

There are randomized fully dynamic algorithms with polylogarithmic worst-case update time that maintain an estimate of the maximum matching size with approximation ratio

1. $1 + \frac{1}{\sqrt{2}} + \varepsilon \approx 1.707 + \varepsilon$ on bipartite graphs, and
2. $1.973 + \varepsilon$ on general graphs,

for every constant $\varepsilon > 0$, with approximation and worst-case update time guarantees holding with high probability against an adaptive adversary (Bhattacharya-Kiss-Saranurak-Wajc). Independently, Behnezhad gives a randomized algorithm with polylogarithmic worst-case update time maintaining a matching-size estimate of at least $0.501\,\mu(G)$ against adaptive adversaries; for bipartite graphs the ratio improves to $0.585$ against oblivious and $0.542$ against adaptive adversaries.

## Proof sketch

Both results are value versions: they maintain a maximal-matching-type structure (an approximately maximal matching robust to adaptive updates) and estimate how much a second augmentation pass would gain. The second pass of a two-pass streaming matching algorithm is simulated by calling a sublinear-time matching-size estimator in a white-box way, which avoids paying for vertex updates explicitly. Sampling-based estimation of the gain gives a constant-factor improvement over $2$ without maintaining the matching itself.

## Depends on

- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Wajc: dynamic rounding of fractional matchings against adaptive adversaries](wajc-adaptive-rounding-theorem.md)

## Sources

- Sayan Bhattacharya, Peter Kiss, Thatchaphol Saranurak, David Wajc, "Dynamic Matching with Better-than-2 Approximation in Polylogarithmic Update Time", SODA (2023), arXiv:2207.07438.
- Soheil Behnezhad, "Dynamic Algorithms for Maximum Matching Size", SODA (2023), arXiv:2207.07607.
