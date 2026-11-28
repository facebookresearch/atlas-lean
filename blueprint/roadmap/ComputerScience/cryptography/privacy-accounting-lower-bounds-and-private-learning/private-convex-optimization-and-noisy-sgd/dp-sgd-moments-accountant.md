# Moments accountant privacy bound for DP-SGD

There are absolute constants $c_1, c_2$ such that, for DP-SGD (add/remove adjacency, clipping norm $C$, noise standard deviation $\sigma C$) with Poisson sampling rate $q$ and $T$ steps, in the parameter range $\sigma \ge 1$ and $q < 1/(16\sigma)$ used by the analysis, for every $0 < \varepsilon < c_1 q^2 T$ and $0 < \delta < 1$, the algorithm is $(\varepsilon, \delta)$-differentially private whenever

$$
\sigma \ge c_2\, \frac{q\sqrt{T\log(1/\delta)}}{\varepsilon}.
$$

The positivity of $\varepsilon$ and $\delta < 1$ make the right-hand side a finite real number; for $\delta \ge 1$ every mechanism is trivially $(\varepsilon,\delta)$-differentially private, and $\varepsilon = 0$ is not covered. Compared with applying the strong composition theorem to the subsampled Gaussian mechanism, this saves a factor $\sqrt{\log(T/\delta)}$ in $\varepsilon$ and a factor $Tq$ in $\delta$. The same bound follows from Rényi or zCDP-style accounting of the subsampled Gaussian mechanism.

## Proof sketch

Track the log moment generating function of the privacy loss, $\alpha_M(\lambda) = \sup \log\mathbb{E}[e^{\lambda L}]$, the supremum over neighbouring datasets and auxiliary inputs. Under adaptive composition it is bounded by the sum of the per-step log moments, $\alpha_M(\lambda) \le \sum_i \alpha_{M_i}(\lambda)$, not equal to it in general. For the subsampled Gaussian mechanism with sensitivity-$1$ queries, examples included independently with probability $q < 1/(16\sigma)$, $\sigma \ge 1$, and positive integers $\lambda \le \sigma^2\ln(1/(q\sigma))$, a careful expansion of the mixture's likelihood ratio gives $\alpha(\lambda) \le q^2\lambda(\lambda+1)/((1-q)\sigma^2) + O(q^3\lambda^3/\sigma^3)$. Summing these bounds over $T$ steps and applying the tail bound $\delta = \min_\lambda \exp(T\alpha(\lambda) - \lambda\varepsilon)$ gives the stated condition.

## Depends on

- [Differentially private stochastic gradient descent](dp-sgd.md)

## Proof depends on

- [Conversion from zCDP to approximate differential privacy](../zero-concentrated-differential-privacy/zcdp-to-approximate-dp.md)
- [Tight privacy amplification by subsampling](../shuffle-model-and-privacy-amplification/privacy-amplification-by-subsampling.md)

## Sources

- M. Abadi, A. Chu, I. Goodfellow, H. B. McMahan, I. Mironov, K. Talwar, L. Zhang, "Deep Learning with Differential Privacy", ACM CCS (2016), arXiv:1607.00133, Theorems 1 and 2 and Lemma 3.
- I. Mironov, "Renyi Differential Privacy", IEEE CSF (2017), arXiv:1702.07476.
