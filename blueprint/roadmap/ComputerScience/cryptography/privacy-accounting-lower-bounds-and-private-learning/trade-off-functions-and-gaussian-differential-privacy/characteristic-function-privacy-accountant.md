# Privacy loss distributions compose by convolution and are tracked exactly by characteristic functions

For a mechanism $M$, a pair of distributions $(P, Q)$ is a **dominating pair** if $\sup_{D \simeq D'} H_\alpha(M(D) \,\|\, M(D')) \le H_\alpha(P \,\|\, Q)$ for every $\alpha \ge 0$, where $H_\alpha(P \,\|\, Q) = \sup_E \bigl(P(E) - \alpha Q(E)\bigr)$ is the hockey-stick divergence; it is tightly dominating if equality holds for every $\alpha$. Assume first that $P$ and $Q$ are mutually absolutely continuous, and let the **privacy loss random variable** be $L = \log\frac{dP}{dQ}(Y)$ with $Y \sim P$, with characteristic function $\phi_L(t) = \mathbb{E}[e^{itL}]$. If $(P, Q)$ dominates $M$ and $(P', Q')$ dominates $M'$ for every value of $M$'s output, then $(P \times P', Q \times Q')$ dominates the adaptive composition $(M, M')$; for the product pair the privacy loss variables add independently, so their laws convolve and characteristic functions multiply, $\phi_{L_1 + L_2} = \phi_{L_1}\phi_{L_2}$. The privacy profile of the composed pair, $\delta(\varepsilon) = H_{e^{\varepsilon}}(P \times P' \,\|\, Q \times Q') = \mathbb{E}\bigl[(1 - e^{\varepsilon - L})_+\bigr]$ (with $L$ the composed loss under $P \times P'$), can be recovered from the characteristic function by Fourier inversion and converts losslessly to the trade-off function and to Rényi divergences of the same pair. This unifies Rényi accounting, privacy profiles, $f$-DP and privacy loss distribution accounting.

The composed profile is an upper bound on the privacy profile of the composed mechanism, not in general its exact profile: a constant mechanism has exact $\delta(\varepsilon) = 0$ even when a nontrivial pair dominates it. It is exact when each pair is tightly dominating and attained by neighbouring datasets that are worst-case simultaneously for the composed mechanism, for example for the non-adaptive composition of mechanisms that share a worst-case pair of datasets. If $P$ has mass $m$ singular to $Q$, the privacy loss equals $+\infty$ with probability $m$; this atom must be carried separately (the finite part of the law is a defective distribution with total mass $1 - m$, and $\delta(\varepsilon) \ge m$ for every $\varepsilon$), and the characteristic function above is applied only to the finite part.

## Proof sketch

The privacy profile of a pair is the hockey-stick divergence $\sup_E (P(E) - e^{\varepsilon}Q(E)) = \mathbb{E}_P[(1 - e^{\varepsilon - L})_+]$, a functional of the law of $L$ (including its atom at $+\infty$). Domination of the composition follows by conditioning on the first output and applying the domination of the second mechanism for each value, which is why only an inequality results. For product distributions the log-likelihood ratio is the sum of the coordinate log-likelihood ratios, which are independent, so laws convolve and characteristic functions multiply. Inversion via the Lévy formula expresses the distribution function of $L$, hence $\delta(\varepsilon)$, as an integral of $\phi_L$, which is numerically stable with Gaussian quadrature.

## Depends on

- [f-differential privacy](f-differential-privacy.md)

## Proof depends on

- [Lossless adaptive composition of f-differential privacy](f-dp-adaptive-composition.md)
- [Primal–dual conversion between f-DP and families of approximate DP guarantees](f-dp-primal-dual-conversion.md)

## Sources

- Y. Zhu, J. Dong, Y.-X. Wang, "Optimal Accounting of Differential Privacy via Characteristic Function", AISTATS (2022), arXiv:2106.08567, Definitions 7 and 12, Theorem 10 and Proposition 13.
- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
