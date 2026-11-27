# Finite Littlestone dimension implies private learnability

Every class $H$ of Littlestone dimension $d < \infty$ has a $2^{-2^{O(d)}}$-globally stable realizable learner with sample size depending only on $d$ and the accuracy, and hence an $(\varepsilon,\delta)$-differentially private PAC learner with sample complexity

$$
2^{2^{O(d)}} \cdot \mathrm{poly}\big(1/\alpha, 1/\varepsilon, \log(1/\beta), \log(1/\delta)\big).
$$

Together with the $\Omega(\log^* d)$ lower bound, a class is privately PAC learnable if and only if it is online learnable, if and only if it has finite Littlestone dimension. The same holds for replicable learnability.

## Proof sketch

Run the Standard Optimal Algorithm on samples augmented with fictitious mistakes: draw a random number of tournaments in which the SOA is fed a sample together with examples where a previous output erred, so that each round of feedback lowers the Littlestone dimension of the version space. At some random depth at most $d$, the SOA output becomes a fixed function of the distribution with probability at least $2^{-2^{O(d)}}$, which is global stability; the stable-histogram lemma converts it into a private learner.

## Depends on

- [Global stability and list replicability of learning rules](../global-stability-and-list-replicability/global-stability-and-list-replicability.md)
- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [Online classification protocol, mistakes and regret](../../../../online-learning-and-boosting/online-classification-protocol-mistakes-and-regret.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Globally stable learners yield private learners via stable histograms](global-stability-to-private-learning.md)
- [Private learning requires log-star of the Littlestone dimension samples](private-learning-requires-log-star-littlestone.md)

## Sources

- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563.
- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949.
