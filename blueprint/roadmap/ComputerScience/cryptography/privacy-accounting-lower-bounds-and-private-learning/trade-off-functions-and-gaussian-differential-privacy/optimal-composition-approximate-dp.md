# Optimal composition theorem for approximate differential privacy

For every $\varepsilon > 0$, $\delta \in [0,1]$ and $k \in \mathbb{N}$, the $k$-fold adaptive composition of $(\varepsilon,\delta)$-differentially private mechanisms is

$$
\Big( (k - 2i)\varepsilon,\; 1 - (1-\delta)^k (1 - \delta_i) \Big)\text{-DP} \quad \text{for every } i \in \{0, 1, \dots, \lfloor k/2 \rfloor\},
$$

where

$$
\delta_i = \frac{\sum_{\ell=0}^{i-1} \binom{k}{\ell}\big(e^{(k-\ell)\varepsilon} - e^{(k-2i+\ell)\varepsilon}\big)}{(1 + e^{\varepsilon})^k},
$$

and this family of guarantees is exactly optimal: for each $i$ there are $(\varepsilon,\delta)$-DP mechanisms whose $k$-fold composition is not $((k-2i)\varepsilon, \delta')$-DP for any $\delta' < 1 - (1-\delta)^k(1-\delta_i)$. In trade-off-function language, with $f_{\varepsilon,\delta}(\alpha) = \max\{0,\, 1 - \delta - e^{\varepsilon}\alpha,\, e^{-\varepsilon}(1 - \delta - \alpha)\}$ the trade-off function of $(\varepsilon,\delta)$-DP, the composition is exactly $f_{\varepsilon,\delta}^{\otimes k}$-DP.

## Proof sketch

The argument is pairwise. Fix a pair of neighbouring datasets $D_0, D_1$. For each step $j$ and each past transcript, the two conditional output laws of the $j$-th mechanism on $D_0$ and $D_1$ form an $(\varepsilon,\delta)$-indistinguishable pair, so they are obtained from the canonical four-point pair representing $f_{\varepsilon,\delta}$ (randomized response that reveals the hypothesis with probability $\delta$) by a Markov kernel that depends on this pair of datasets and on the past transcript; one binary-input primitive does not simulate a whole arbitrary-input mechanism with a single kernel. Running these kernels step by step on independent copies of the canonical pair reproduces the joint output laws on $D_0$ and $D_1$, so by the data processing inequality the composition on this pair is dominated by the $k$-fold product of the canonical pair. The trade-off function of the product is computed exactly by a binomial count of the number of coordinates that point to each hypothesis, which yields the stated piecewise linear envelope; the canonical pair itself attains it.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)
- [f-differential privacy](f-differential-privacy.md)
- [Tensor product of trade-off functions](tensor-product-of-trade-off-functions.md)

## Proof depends on

- [Approximate differential privacy as f-differential privacy](epsilon-delta-dp-as-f-dp.md)
- [Lossless adaptive composition of f-differential privacy](f-dp-adaptive-composition.md)

## Sources

- P. Kairouz, S. Oh, P. Viswanath, "The Composition Theorem for Differential Privacy", ICML (2015); IEEE Transactions on Information Theory 63 (2017), arXiv:1311.0776, Theorems 2.4, 2.5 and 3.3.
