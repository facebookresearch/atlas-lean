# Optimal linear filter for Poisson case counts

**Model.** A hidden epidemic state $\vec x_k \in \mathbb{R}^d$ (for example compartment sizes) and observed counts $\vec y_k$ (patients presenting each day) follow

$$\vec x_k = F\vec x_{k-1} + \vec b_k + \vec\omega_{k-1}, \qquad \vec y_k \sim \mathrm{Poisson}(B\vec x_k)\ \text{(componentwise, conditionally on } \vec x_k),$$

with known matrices $F$, $B$, known forcing $\vec b_k$, and dynamical noise $\vec\omega_k$ of mean zero and covariance $W$, independent of everything else. A linear filter has the form $\hat x_k = A_1\hat x_{k-1} + A_2\vec y_k$.

**Key lemma.** If $\lambda$ is any random variable and $z \mid \lambda \sim \mathrm{Poisson}(\lambda)$, then $\mathbb{E}\big[(\lambda - \mathbb{E}\lambda)(z - \mathbb{E}[z \mid \lambda])\big] = 0$: the Poisson observation noise $z - \lambda$ is uncorrelated with the signal, although its variance $\lambda$ depends on it.

**Poisson Kalman filter.** Forecast $\hat x_k^- = F\hat x_{k-1}^+$ (plus the known forcing), $P_k^- = FP_{k-1}^+F^\top + W$; assimilate

$$\hat x_k^+ = \hat x_k^- + K_k\big(\vec y_k - B\hat x_k^-\big), \qquad K_k = P_k^-B^\top\big(BP_k^-B^\top + V_k\big)^{-1}, \qquad V_k = \mathrm{diag}(B\vec x_k),$$

$$P_k^+ = (I - K_kB)P_k^-(I - K_kB)^\top + K_kV_kK_k^\top.$$

**Theorem.**
1. If $\mathbb{E}\hat x_0^+ = \vec x_0$, then for every choice of gains $K_k$ the two-step filter is unbiased: $\mathbb{E}\hat x_k^+ = \vec x_k$ for all $k$.
2. Among all linear filters, the gain $K_k$ above with $V_k = \mathrm{diag}(B\vec x_k)$ minimizes the expected sum of squared errors $J_k = \mathbb{E}\|\hat x_k^+ - \vec x_k\|^2$, i.e. $\partial J_k/\partial K_k = 0$ at this gain.
The same optimality holds for the corresponding recursive least-squares estimator with gain $K_k = P_{k-1}B^\top(BP_{k-1}B^\top + V_k)^{-1}$.

## Proof sketch

Because Poisson noise is conditionally mean-zero, the innovation $\vec y_k - B\hat x_k^-$ has mean zero whenever the forecast is unbiased, which gives unbiasedness for any gain by induction. The lemma removes the cross term between state error and observation noise in the error covariance, so $J_k = \mathrm{tr}\,P_k^+$ has the same quadratic dependence on $K_k$ as in the Gaussian Kalman filter, with the observation covariance replaced by the state-dependent Poisson variance $\mathrm{diag}(B\vec x_k)$; setting the derivative to zero gives the Kalman-type gain. In practice the unknown $\vec x_k$ in $V_k$ is replaced by the current estimate, and an extended version linearizes a nonlinear SIR-type model with a hospitalized compartment, used to track and forecast influenza-like illness counts.

## Sources

- Donald Ebeigbe, Tyrus Berry, Steven J. Schiff and Timothy Sauer, "Poisson Kalman filter for disease surveillance", *Physical Review Research* 2 (2020), 043028, <https://doi.org/10.1103/physrevresearch.2.043028>. Preprint version: arXiv:2003.11194 (2020), Lemma 2.1, Theorems 2.2 and 2.3 (Section 2), Theorems A.1 and A.2 (Appendix A), <https://doi.org/10.48550/arXiv.2003.11194>.
