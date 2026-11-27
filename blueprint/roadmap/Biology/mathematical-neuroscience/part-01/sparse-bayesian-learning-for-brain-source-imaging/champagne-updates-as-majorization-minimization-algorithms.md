# Champagne updates as majorization–minimization algorithms

**Model.** Sensor data $y(t) \in \mathbb{R}^M$, $t = 1,\dots,T$, satisfy $y(t) = L x(t) + \varepsilon(t)$ with lead field $L \in \mathbb{R}^{M \times N}$ (columns $L_n$), Gaussian noise $\varepsilon(t) \sim \mathcal{N}(0, \sigma^2 I)$ and sources $x(t) \sim \mathcal{N}(0, \Gamma)$ independently over $t$, $\Gamma = \operatorname{diag}(\gamma)$, $\gamma \in \mathbb{R}^N_{\ge 0}$. The posterior of the sources is Gaussian with

$$\bar x(t) = \Gamma L^{\mathsf T}\Sigma_y^{-1} y(t),\qquad \Sigma_x = \Gamma - \Gamma L^{\mathsf T}\Sigma_y^{-1} L\Gamma,\qquad \Sigma_y = \sigma^2 I + L\Gamma L^{\mathsf T},$$

and the Type-II (negative log marginal likelihood) cost is

$$\mathcal{L}_{II}(\gamma) = \frac1T\sum_{t=1}^T y(t)^{\mathsf T}\Sigma_y^{-1} y(t) + \log|\Sigma_y| = \operatorname{tr}(C_y \Sigma_y^{-1}) + \log|\Sigma_y|,$$

with $C_y$ the sample covariance; it is non-convex in $\gamma$.

**MM framework.** A sequence $u^{k+1} = \arg\min_u g(u \mid u^k)$ is a majorization–minimization (MM) algorithm for $f$ if [A1] $g(u^k \mid u^k) = f(u^k)$, [A2] $g(u \mid u^k) \ge f(u)$ for all $u$, and [A3] $u^{k+1}$ minimizes $g(\cdot \mid u^k)$. Then $f(u^{k+1}) \le f(u^k)$ (Corollary 1). If moreover [A4] $\nabla g(u \mid u^k)|_{u=u^k} = \nabla f(u^k)$, every limit point of $(u^k)$ is a stationary point of $f$ (Theorem 1).

**Unification.** The three classical Champagne updates are MM algorithms:

- *EM Champagne* (Proposition 1), $\gamma_n^{k+1} = (\Sigma_x^k)_{n,n} + \frac1T\sum_t \bar x_n^k(t)^2$, majorizes $-\log p(Y \mid \gamma)$ by the Jensen (expected complete-data) bound and has the descent property.
- *Convex-bounding Champagne* (Proposition 2), $z_n^k = L_n^{\mathsf T}(\Sigma_y^k)^{-1}L_n$ and $\gamma_n^{k+1} = \sqrt{\frac1T\sum_t \bar x_n^k(t)^2 / z_n^k}$, majorizes the concave term $\log|\Sigma_y|$ by its tangent plane at $\gamma^k$ and satisfies [A1]–[A4].
- *MacKay-update Champagne* (Proposition 3) minimizes the same tangent-plane surrogate by a fixed-point iteration and satisfies [A1]–[A4].

**Low-SNR surrogate (Proposition 4).** With $\sigma^2$ normalized to 1, $\mathcal{L}^{\text{Low-SNR}}_{\text{conv}}(\gamma \mid \gamma^k) = \operatorname{tr}(L\Gamma L^{\mathsf T}) + \frac1T\sum_t y(t)^{\mathsf T}\Sigma_y^{-1}y(t)$ majorizes $\mathcal{L}_{II}$ ([A2]) but is not tangent to it at $\gamma^k$, so [A1] and [A4] fail and its minimization need not decrease $\mathcal{L}_{II}$ or converge to a stationary point; $\mathcal{L}_{II}(\gamma) = \mathcal{L}^{\text{Low-SNR}}_{\text{conv}}(\gamma\mid\gamma^k) + O(\mathrm{SNR})$ as the signal-to-noise ratio tends to zero.

## Depends on

- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)
- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Descent follows from the sandwich $f(u^{k+1}) \le g(u^{k+1}\mid u^k) \le g(u^k \mid u^k) = f(u^k)$. For EM, Jensen's inequality applied to $-\log \mathbb{E}_{p(X\mid\gamma)} p(Y \mid X)$ with the current posterior as importance distribution gives the surrogate, whose minimizer is the M-step; condition [A3] holds because $\log|\Gamma|$ is geodesically convex on positive definite matrices, so local minima of the surrogate are global. For convex bounding, concavity of $\gamma \mapsto \log|\sigma^2 I + L\operatorname{diag}(\gamma)L^{\mathsf T}|$ gives $\log|\Sigma_y| \le \log|\Sigma_y^k| + \operatorname{tr}\big((\Sigma_y^k)^{-1}(\Sigma_y - \Sigma_y^k)\big)$, which is linear in $\gamma$ with slopes $z_n^k$; together with the variational form $\frac1T\sum_t \bar x_n(t)^2/\gamma_n$ the surrogate separates over $n$ and its minimizer is the square-root update. For the low-SNR bound, $\log|I + L\Gamma L^{\mathsf T}| = \sum_i \log(1 + p_i)$ over eigenvalues $p_i$ of $L\Gamma L^{\mathsf T}$ is at most $\sum_i p_i = \operatorname{tr}(L\Gamma L^{\mathsf T})$, with equality to first order as the $p_i \to 0$.

## Sources

- A. Hashemi, C. Cai, G. Kutyniok, K.-R. Müller, S. S. Nagarajan, S. Haufe, "Unification of sparse Bayesian learning algorithms for electromagnetic brain imaging with the majorization minimization framework", NeuroImage 239 (2021) 118309, Section 2.3 (Eqs. (7)–(19)), Section 3 (conditions [A1]–[A4], Corollary 1, Theorem 1, Propositions 1–3), Section 4 (Eq. (27), Proposition 4) and Appendices B–F, <https://doi.org/10.1016/j.neuroimage.2021.118309>, PMCID PMC8433122.
