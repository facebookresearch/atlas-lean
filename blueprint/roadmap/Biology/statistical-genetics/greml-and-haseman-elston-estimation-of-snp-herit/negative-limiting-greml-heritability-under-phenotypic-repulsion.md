# GREML converges to a negative heritability when genetic similarity lowers phenotypic variance

**Setting.** Let $A_n$ be an $n\times n$ genetic relationship matrix with eigenvector matrix $U^{(n)}$ and eigenvalues $s_{n,i}^2\ge0$, normalized so that $\sum_i s_{n,i}^2=n$. The GREML random-effects model with heritability $\psi$ and noise precision $\theta$ takes $y\sim\mathrm{MVN}\bigl(0,\theta^{-1}(\varphi A_n+I_n)\bigr)$, $\varphi=\psi/(1-\psi)$; after rotation $z=U^{(n)\top}y$ the $z_i$ are independent with variances $\theta^{-1}(1+\psi(s_{n,i}^2-1))/(1-\psi)$. Let $\hat\psi_n$ be the maximum-likelihood estimate of $\psi$ in this model, over the values where the model covariance is positive definite.

**Proposition 1 (Steinsaltz, Dahl and Wachter).** Assume

- $s_{\max}^2:=\limsup_{n\to\infty}\max_{1\le i\le n}s_{n,i}^2<\infty$;
- $\sup_n n^{-1}\sum_{i=1}^n s_{n,i}^{-12}<\infty$;
- $1<C_2+1:=\liminf_{n\to\infty}n^{-1}\sum_{i=1}^n s_{n,i}^4$, and put $C_3:=\limsup_{n\to\infty}n^{-1}\sum_{i=1}^n s_{n,i}^4$.

Suppose the data are in fact $y^{(n)}\sim\mathrm{MVN}\bigl(0,\ U^{(n)}\operatorname{diag}(f(s_{n,i}^2))\,U^{(n)\top}\bigr)$ for a positive, strictly decreasing, continuously differentiable $f:\mathbb R_+\to\mathbb R_+$ with

$$C_1:=\inf_{0\le t\le s_{\max}^2}\bigl(-f'(t)\bigr)>0.$$

Put

$$\delta:=\frac16\left(\frac{C_3\,f(0)}{C_1C_2}+s_{\max}^2-1\right)^{-1}>0.$$

Then $\mathbb P(\hat\psi_n>-\delta)\to0$ as $n\to\infty$: the misspecified GREML estimate is bounded above in probability by a strictly negative number.

**Phenotypic repulsion.** Multiply the GREML density with true parameters $(\theta_0,\varphi_0)$ by the penalty $\exp\{-\alpha\theta_0(\sum_{i<j}A_{ij}y_iy_j+\tfrac12\sum_i(A_{ii}-1)y_i^2)\}=\exp\{-\tfrac{\alpha\theta_0}2\,y^\top(A-I_n)y\}$, with repulsion parameter $\alpha\le1$, so that genetically similar individuals are pushed toward dissimilar phenotypes. The phenotypes are then $\mathrm{MVN}\bigl(0,\theta_0^{-1}[(\varphi_0A+I_n)^{-1}+\alpha(A-I_n)]^{-1}\bigr)$, which is the setting above with

$$f(t)=\frac{1+\varphi_0t}{1-\alpha+\alpha(1-\varphi_0)t+\alpha\varphi_0t^2},\qquad f'(t)=\frac{\varphi_0-\alpha(1+\varphi_0t)^2}{\bigl(1-\alpha+\alpha(1-\varphi_0)t+\alpha\varphi_0t^2\bigr)^2}$$

(up to the constant factor $\theta_0^{-1}$). When $\varphi_0<\alpha$, $f'(t)<0$ for all $t\ge0$, so GREML targets a negative heritability even though the additive genetic variance $\varphi_0\ge0$. With $\theta_0 = 1$, the Haseman–Elston estimate $\hat\sigma_g^2 = n^{-1}y^\top(A_n - I_n)y \,/\, (n^{-1}\operatorname{tr}(A_n^2) - 1)$, which uses the diagonal entries of $A_n$ as well as the off-diagonal ones, satisfies $\mathbb{P}(\hat\sigma_g^2 < -C_1 C_2/C_3) \to 1$ as $n \to \infty$.

## Depends on

- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](greml-cov.md)
- [Spectral REML criterion for GREML variance components](spectral-log-lik.md)

## Expansion

- In the rotated coordinates the GREML likelihood is a product over eigen-directions, and the estimates solve $0=\operatorname{Cov}(w(\hat\psi),v(\hat\psi))$ and $\hat\theta=n/\sum_iv_i(\hat\psi)$, with $w_i(\psi)=(1-\psi)/(1+\psi(s_i^2-1))$, $v_i=w_iz_i^2$ and $\operatorname{Cov}$ the empirical covariance across $i$. To first order $\log z_i^2$ is linear in $s_i^2$ with slope $\psi_0$, so heritability acts as the slope of phenotypic variance on relatedness eigenvalues, which can be negative.
- The proof passes to subsequences along which the empirical eigenvalue distribution converges weakly, uses the principle that a misspecified maximum-likelihood estimate converges to the Kullback–Leibler closest fit, and shows that the limiting score is negative on $[-\delta,\infty)$ because $f(s^2)$ is negatively correlated with $s^2$ (Harris's inequality). A uniform-convergence lemma replaces the i.i.d. arguments, which do not apply.
- The condition $\varphi_0<\alpha$ follows from the explicit derivative: the numerator $\varphi_0-\alpha(1+\varphi_0t)^2\le\varphi_0-\alpha<0$ for $t\ge0$, $\varphi_0\ge0$.
- The negative-moment bound (Eq. (9) of the source) forces every eigenvalue $s_{n,i}^2$ to be positive, so it excludes relationship matrices with a zero eigenvalue, such as a centred GRM; the proof uses it to bound $n^{-1}\sum_i|a_{n,i}(\psi)|$ and $n^{-1}\sum_i|a'_{n,i}(\psi)|$ uniformly in $n$ and $\psi\in[-\delta,1]$ (Appendix A).

## Sources

- D. Steinsaltz, A. Dahl, K. W. Wachter, *On negative heritability and negative estimates of heritability*, Genetics 215 (2020), 343–357, <https://doi.org/10.1534/genetics.120.303161>, PMCID PMC7268991 (Equations 1–4 and 6–12, Proposition 1, Appendix A, Appendix B).
