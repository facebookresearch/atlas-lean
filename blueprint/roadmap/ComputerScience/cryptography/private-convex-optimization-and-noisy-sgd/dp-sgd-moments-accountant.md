# Moments accountant privacy bound for DP-SGD

There are absolute constants $c_1, c_2$ such that, for DP-SGD with sampling rate $q$ and $T$ steps, for every $\varepsilon < c_1 q^2 T$ and $\delta > 0$, the algorithm is $(\varepsilon, \delta)$-differentially private whenever

$$
\sigma \ge c_2\, \frac{q\sqrt{T\log(1/\delta)}}{\varepsilon}.
$$

Compared with applying the strong composition theorem to the subsampled Gaussian mechanism, this saves a factor $\sqrt{\log(T/\delta)}$ in $\varepsilon$ and a factor $Tq$ in $\delta$. The same bound follows from Rényi or zCDP-style accounting of the subsampled Gaussian mechanism.

## Proof sketch

Track the log moment generating function of the privacy loss, $\alpha_M(\lambda) = \sup \log\mathbb{E}[e^{\lambda L}]$, which is additive under adaptive composition. For the subsampled Gaussian mechanism with $\sigma \ge 1$ and $\lambda \le \sigma^2\log(1/(q\sigma))$, a careful expansion of the mixture's likelihood ratio gives $\alpha(\lambda) \le q^2\lambda(\lambda+1)/((1-q)\sigma^2) + O(q^3\lambda^3/\sigma^3)$. Summing over $T$ steps and applying the tail bound $\delta = \min_\lambda \exp(T\alpha(\lambda) - \lambda\varepsilon)$ gives the stated condition.

## Depends on

- [Differentially private stochastic gradient descent](dp-sgd.md)
- [Conversion from zCDP to approximate differential privacy](../zero-concentrated-differential-privacy/zcdp-to-approximate-dp.md)
- [Tight privacy amplification by subsampling](../shuffle-model-and-privacy-amplification/privacy-amplification-by-subsampling.md)

## Proof depends on

- [Differentially private stochastic gradient descent](dp-sgd.md)
- [Conversion from zCDP to approximate differential privacy](../zero-concentrated-differential-privacy/zcdp-to-approximate-dp.md)
- [Tight privacy amplification by subsampling](../shuffle-model-and-privacy-amplification/privacy-amplification-by-subsampling.md)

## Sources

- M. Abadi, A. Chu, I. Goodfellow, H. B. McMahan, I. Mironov, K. Talwar, L. Zhang, "Deep Learning with Differential Privacy", ACM CCS (2016), arXiv:1607.00133.
- I. Mironov, "Renyi Differential Privacy", IEEE CSF (2017), arXiv:1702.07476.
