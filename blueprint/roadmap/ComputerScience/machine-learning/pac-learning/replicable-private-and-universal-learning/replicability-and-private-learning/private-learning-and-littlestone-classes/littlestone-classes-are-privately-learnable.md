# Finite Littlestone dimension implies private learnability

Every class $H$ of Littlestone dimension $d < \infty$ has, for every $\alpha > 0$, a realizable learner on $m = 2^{2^{d+2}+1} 4^{d+1} \lceil 2^{d+2}/\alpha \rceil$ samples that outputs some hypothesis of error at most $\alpha$ with probability at least $\big((d+1) 2^{2^d+1}\big)^{-1}$, and hence, for all $\varepsilon, \delta \in (0,1)$ and $\alpha, \beta \in (0, 1/2)$, an $(\varepsilon,\delta)$-differentially private PAC learner with sample complexity

$$
O\!\left(\frac{2^{\tilde O(2^d)} + \log(1/(\beta\delta))}{\alpha\, \varepsilon}\right).
$$

Together with the $\Omega(\log^* d)$ lower bound, a class is approximately differentially privately PAC learnable if and only if it is online learnable, if and only if it has finite Littlestone dimension.

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

- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563, Theorems 1, 3 and 10.
- N. Alon, R. Livni, M. Malliaris, S. Moran, "Private PAC Learning Implies Finite Littlestone Dimension", STOC (2019), arXiv:1806.00949, Corollary 2.
