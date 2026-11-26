# Decorrelated Mendelian randomization test after association screening

**Model.** Observations are i.i.d. copies of $(X,Y,G_1,\dots,G_K)$ from the linear structural model with $K$ fixed, pairwise uncorrelated variants $G_j$ (variance $\sigma^2_{G_j}$), unobserved confounder $U$ and independent noises:

$$X=\sum_{j=1}^K\alpha_jG_j+U+\varepsilon_1,\qquad Y=\gamma X+\lambda U+\varepsilon_2 ,$$

with $G$ independent of $(U,\varepsilon_1,\varepsilon_2)$, finite fourth moments and relevant instruments. Let $\hat\beta_{XY}$ be the observational OLS slope of $Y$ on $X$ (the *screening* statistic) and $\hat\theta_n$ the MR estimator of $\gamma$ (Wald ratio for $K=1$, fixed-effect IVW with weights $\pi_j$ for $K>1$).

**Joint limit.** With $V_X=\operatorname{Var}X$,

$$\sqrt n\begin{pmatrix}\hat\beta_{XY}-\beta_{XY}\\ \hat\theta_n-\gamma\end{pmatrix}\xrightarrow{d}N\Bigl(0,\begin{pmatrix}\omega_{11}&\omega_{12}\\ \omega_{12}&\omega_{22}\end{pmatrix}\Bigr),\qquad \omega_{12}=\frac{\lambda^2\sigma_U^2+\sigma^2_{\varepsilon_2}}{V_X}-\frac{2\lambda^2\sigma_U^4}{V_X^2},$$

$\omega_{11}=\mathbb E\{X^2(Y-\beta_{XY}X)^2\}/V_X^2$, and $\omega_{22}=(\lambda^2\sigma_U^2+\sigma^2_{\varepsilon_2})/(\alpha^2\sigma_G^2)$ for the Wald ratio, $\omega_{22}=(\lambda^2\sigma_U^2+\sigma^2_{\varepsilon_2})\sum_j\pi_j^2\alpha_j^2/\sigma^2_{G_j}\big/(\sum_j\pi_j\alpha_j^2)^2$ for IVW. Under confounding $\omega_{12}\neq0$, so testing $H_0:\gamma=\gamma_0$ only for pairs whose association passed a screen on $\hat\beta_{XY}$ tilts the null law of the standard MR statistic and inflates the conditional type I error; screening is harmless only when the correlation is zero.

**Decorrelated statistics.** Let $r=\omega_{12}/\omega_{11}$ and $V_0=\omega_{22}-\omega_{12}^2/\omega_{11}$. Given an independent external estimate $\hat\beta^{(s)}_{XY}$ from a sample of size $m$ with $\sqrt m(\hat\beta^{(s)}_{XY}-\beta_{XY})\to N(0,\omega_{11})$ and $n/m\to\eta\in(0,\infty)$, define

$$U_1=\frac{\hat\theta_n-\gamma_0-r\bigl(\hat\beta_{XY}-\hat\beta^{(s)}_{XY}\bigr)}{\sqrt{V_1/n}},\qquad V_1=\omega_{22}+\Bigl(\frac nm-1\Bigr)\frac{\omega_{12}^2}{\omega_{11}} ,$$

and let $U_2$ be $U_1$ with $r,V_1$ replaced by influence-function plug-in estimates.

**Theorem.** Suppose $\Omega$ is positive definite. Under $H_0$, $U_1\to N(0,1)$ and $U_2-U_1=o_p(1)$; under local alternatives $\gamma=\gamma_0+\Delta/\sqrt n$, $U_2\to N(\Delta/\sqrt{V_1},1)$. Moreover, for any screening event $A_n$ determined in the limit by $\sqrt n(\hat\beta_{XY}-\beta_{XY})$, with positive limiting probability and null boundary, $\mathcal L(U_2\mid A_n)\Rightarrow N(0,1)$ under $H_0$: the test keeps its nominal level conditionally on having passed the screen. The oracle version $U_0$ (true $\beta_{XY}$ in place of $\hat\beta^{(s)}_{XY}$, variance $V_0$) has the same property.

## Expansion

Both estimators are asymptotically linear with influence functions $\phi_1=X(Y-\beta_{XY}X)/V_X$ and, for the Wald ratio, $\phi_2=G(Y-\gamma X)/(\alpha\sigma_G^2)$; the delta method gives the joint Gaussian limit. Subtracting $r\hat\beta_{XY}$ removes the component of $\hat\theta_n$ linearly predictable from the screening statistic, so the corrected numerator has zero first-order covariance with $\hat\beta_{XY}$ and, being jointly Gaussian in the limit, is independent of any screening event built from it. Replacing the unknown $\beta_{XY}$ by an independent estimate adds the variance $r^2\omega_{11}/m$; when $m>n$ and $\omega_{12}\neq0$ this makes $V_1<\omega_{22}$, so external association data increase power.

## Sources

- L. Jia, B. Chen, "When Screening Misleads: A Robust Mendelian Randomization Test for Reliable Causal Discovery", arXiv:2607.10755 (2026), Section 2 (selected null distribution), Section 3 (Assumption 1, Lemma 1, Theorems 1–2) and Section 4 (oracle and external-association theorems, Proposition 1 and the feasible post-screening theorem). <https://doi.org/10.48550/arXiv.2607.10755>
