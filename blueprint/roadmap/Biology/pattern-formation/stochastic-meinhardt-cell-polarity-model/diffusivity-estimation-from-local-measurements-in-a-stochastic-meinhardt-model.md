# Diffusivity estimation from local measurements in a stochastic Meinhardt cell-polarity model

**Model.** On the cell contour $\Lambda = \mathbb{R}/(L\mathbb{Z})$, an activator $A$ and inhibitor $I$ obey the stochastic Meinhardt reaction–diffusion system

$$\partial_t A = D_A\partial_x^2 A + f_A(A, I, x) + \sigma_A\xi_A, \qquad \partial_t I = D_I\partial_x^2 I + f_I(A, I) + \sigma_I\xi_I,$$

with independent space-time white noises $\xi_A, \xi_I$,

$$f_A(y, x) = r_A\frac{\zeta(x)(b_A + y_1^2)}{(\zeta_I + |y_2|)(1 + \zeta_A y_1^2)} - r_A y_1, \qquad f_I(y) = b_I y_1 - r_I y_2,$$

and external signal $\zeta(x) = 1 - a\cos(2\pi x/L)$ (e.g. a chemoattractant gradient whose maximum defines the cell front).

**Theorem (well-posedness).** For initial data $(A_0, I_0) \in C^{2+s}(\Lambda; \mathbb{R}^2)$, $0 < s < \tfrac12$, there is a unique mild solution $X = (A, I) \in C([0,T]; C^s(\Lambda; \mathbb{R}^2))$; it decomposes as $X = \bar X + \tilde X$ with $\bar X$ the stochastic convolution solving the linear equation (no reaction terms, zero initial value) and $\tilde X \in C([0,T]; C^{2+s}(\Lambda; \mathbb{R}^2))$ a perturbation process.

**Estimator.** Activator fluorescence is observed through a point spread function: $A_\delta(t, x_k) = \langle A(t), K_{\delta,x_k}\rangle$, $K_{\delta,x_k}(x) = \delta^{-1/2}K((x - x_k)/\delta)$, at $M$ locations, together with $A^\Delta_\delta(t, x_k) = \langle A(t), \partial_x^2 K_{\delta,x_k}\rangle$. The augmented maximum-likelihood estimator (ignoring the nonlinear term) is

$$\hat D_{A,\delta} = \frac{\sum_{k=1}^M\int_0^T A^\Delta_\delta(t, x_k)\,dA_\delta(t, x_k)}{\sum_{k=1}^M\int_0^T \big(A^\Delta_\delta(t, x_k)\big)^2\,dt}.$$

**Theorem (asymptotic normality).** Let $K \in H^2(\mathbb{R})$, $K \ne 0$, have compact support and $\sigma_A > 0$. As the resolution $\delta \to 0$,

$$\delta^{-1}\big(\hat D_{A,\delta} - D_A\big) \xrightarrow{d} N\Big(0,\ D_A\frac{\Sigma}{MT}\Big), \qquad \Sigma = \frac{2\|K\|^2_{L^2(\mathbb{R})}}{\|K'\|^2_{L^2(\mathbb{R})}},$$

so $\hat D_{A,\delta} \pm \delta(MT)^{-1/2}(\hat D_{A,\delta}\Sigma)^{1/2}q_{1-\alpha/2}$ is an asymptotic $(1-\alpha)$ confidence interval. The nonlinearity, the unobserved inhibitor and the signal $\zeta$ do not affect the limit.

## Proof sketch

Each local measurement satisfies $dA_\delta = D_A A^\Delta_\delta\,dt + \langle f_A, K_{\delta,x_k}\rangle dt + \sigma_A\|K\|\,dW_k$, a linear regression on $A^\Delta_\delta$ plus a nuisance drift. The observed Fisher information $\sum_k\int_0^T(A^\Delta_\delta)^2dt$ grows like $\delta^{-2}$, because the rough stochastic convolution dominates second derivatives at fine scales, whereas the reaction term is smoother and contributes only $O_P(\delta^{-1/2})$; a martingale central limit theorem then gives the $\delta$-rate. Without the noise ($\sigma_A = 0$) the estimator is biased, since the nonlinear drift no longer averages out.

## Sources

- Randolf Altmeyer, Till Bretschneider, Josef Janák and Markus Reiß, "Parameter Estimation in an SPDE Model for Cell Repolarization", *SIAM/ASA Journal on Uncertainty Quantification* 10 (2022), 179–199, <https://doi.org/10.1137/20m1373347>. Preprint version: arXiv:2010.06340 (2020), Section 2 (existence and uniqueness theorem) and Section 4 (estimator, asymptotic normality theorem and confidence intervals), <https://doi.org/10.48550/arXiv.2010.06340>.
