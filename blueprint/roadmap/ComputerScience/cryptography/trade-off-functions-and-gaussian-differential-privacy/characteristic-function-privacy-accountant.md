# Privacy loss distributions compose by convolution and are tracked exactly by characteristic functions

For a mechanism and a dominating pair of output distributions $(P, Q)$ (a pair whose hockey-stick divergences upper bound those of every neighbouring pair), let the **privacy loss random variable** be $L = \log\frac{dP}{dQ}(Y)$ with $Y \sim P$ and let $\phi_L(t) = \mathbb{E}[e^{itL}]$. Under adaptive composition, dominating pairs multiply, privacy loss variables add independently, and characteristic functions multiply: $\phi_{L_1 + L_2} = \phi_{L_1}\phi_{L_2}$. The resulting composed privacy profile $\delta(\varepsilon) = \mathbb{E}\big[(1 - e^{\varepsilon - L})_+\big]$ (computed under $P$) is exactly tight, can be recovered from the characteristic function by Fourier inversion, and converts losslessly to $f$-DP and to Rényi guarantees, which unifies Rényi accounting, privacy profiles, $f$-DP and privacy loss distribution accounting.

## Proof sketch

The privacy profile of a pair is the hockey-stick divergence $\sup_E (P(E) - e^{\varepsilon}Q(E)) = \mathbb{E}_P[(1 - e^{\varepsilon - L})_+]$, a functional of the law of $L$. For product distributions the log-likelihood ratio is the sum of the coordinate log-likelihood ratios, which are independent, so laws convolve and characteristic functions multiply. Inversion via the Lévy formula expresses $\delta(\varepsilon)$ as an integral of $\phi_L$, which is numerically stable with Gaussian quadrature.

## Depends on

- [f-differential privacy](f-differential-privacy.md)

## Proof depends on

- [Lossless adaptive composition of f-differential privacy](f-dp-adaptive-composition.md)
- [Primal–dual conversion between f-DP and families of approximate DP guarantees](f-dp-primal-dual-conversion.md)

## Sources

- Y. Zhu, J. Dong, Y.-X. Wang, "Optimal Accounting of Differential Privacy via Characteristic Function", AISTATS (2022), arXiv:2106.08567.
- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
