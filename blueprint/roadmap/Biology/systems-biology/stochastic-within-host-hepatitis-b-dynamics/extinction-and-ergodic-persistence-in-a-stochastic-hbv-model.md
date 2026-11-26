# Extinction and ergodic persistence in a stochastic HBV infection model

**Model.** Uninfected hepatocytes $x$, infected hepatocytes $y$ and free virions $z$ satisfy the Itô system

$$ \begin{aligned} dx &= \big[\Lambda - \mu_1 x - \beta_\eta xz + qy\big]dt + \sigma_1 x\,dW_1,\\ dy &= \big[\beta_\eta xz - (\mu_2 + q)y\big]dt + \sigma_2 y\,dW_2,\\ dz &= \big[p_\epsilon y - \mu_3 z\big]dt + \sigma_3 z\,dW_3, \end{aligned} $$

with independent Brownian motions, $\beta_\eta = (1-\eta)\beta$ and $p_\epsilon = (1-\epsilon)p$ (drug efficacies $\eta, \epsilon$ blocking infection and production), $q$ the cure rate of infected cells, and $\bar x = \Lambda/\mu_1$. The deterministic model has $R_0 = \beta_\eta p_\epsilon \bar x/((\mu_2+q)\mu_3)$, and the spectral abscissa $\lambda_{\max}(J)$ of the infected-subsystem Jacobian at $(\bar x,0,0)$ is negative iff $R_0 < 1$.

**Theorem.**

1. *(Well-posedness.)* For every initial value in $\mathbb R^3_+$ there is a unique global strong solution that stays in the open positive orthant almost surely, with uniformly bounded moments of $x + y + c z$ of some order above $1$.
2. *(Persistence.)* If $\sigma_1, \sigma_2, \sigma_3 > 0$ and

$$ R_0^s = \frac{\beta_\eta p_\epsilon \Lambda}{\big(\mu_1 + \frac{\sigma_1^2}{2}\big)\big(\mu_2 + q + \frac{\sigma_2^2}{2}\big)\big(\mu_3 + \frac{\sigma_3^2}{2}\big)} > 1, $$

   the process is positive recurrent on $\mathbb R^3_+$ with a unique ergodic invariant probability measure. $R_0^s$ reduces to $R_0$ without noise and decreases in each $\sigma_i$.
3. *(Clearance.)* Assume $\mu_1 \le \mu_2$, $3\sigma_1^2 < 2\mu_1$, $3\sigma_2^2 < 2\mu_2$ and $\sigma_2^2 + \sigma_3^2 > 0$. An explicit exponent $\Lambda_{\mathrm{ext}}$, obtained by optimizing over $\alpha > 0$ the Lyapunov functional $\ln(\alpha y + z)$ with a penalty for hepatocyte fluctuations, satisfies almost surely $\limsup_{t\to\infty}\frac1t\ln(y(t) + z(t)) \le \Lambda_{\mathrm{ext}}$ (under an admissibility condition, otherwise with a slightly larger computable exponent), so $\Lambda_{\mathrm{ext}} < 0$ implies exponential clearance. It is sharp in the deterministic limit:

$$ \lambda_{\max}(J) - \tfrac12\max\{\sigma_2^2, \sigma_3^2\} \le \Lambda_{\mathrm{ext}}, $$

   and $\Lambda_{\mathrm{ext}} \to \lambda_{\max}(J)$ as $\sigma_2, \sigma_3 \to 0$ with $\sigma_1^2/(\sigma_2^2 + \sigma_3^2) \to 0$.
4. *(Exclusivity.)* $\Lambda_{\mathrm{ext}} < 0$ implies $R_0^s < 1$, so the clearance and persistence criteria never hold simultaneously; parameters with $R_0^s < 1$ and $\Lambda_{\mathrm{ext}} \ge 0$ are decided by neither criterion.
5. *(Healthy limit law.)* Under clearance, $|x(t) - x_1(t)| \le C_\omega e^{-\gamma_0 t}$ for the linear reference diffusion $dx_1 = (\Lambda - \mu_1 x_1)dt + \sigma_1 x_1\,dW_1$ with the same initial value, whose invariant law is the inverse-gamma distribution with shape $1 + 2\mu_1/\sigma_1^2$ and scale $2\Lambda/\sigma_1^2$ (mean $\bar x$); hence $(x,y,z)(t)$ converges in law to $\pi_1 \otimes \delta_0 \otimes \delta_0$ and time averages of $x^2$ converge to $\bar x^2(1 + \rho_1)$, $\rho_1 = \sigma_1^2/(2\mu_1 - \sigma_1^2)$.

## Expansion

The persistence proof builds a Lyapunov function from $-\ln x$, $-\ln y$, $-\ln z$ and a linear term, whose Itô corrections $\sigma_i^2/2$ enter each removal rate; an arithmetic–geometric mean balance of the three logarithmic terms produces exactly the product in $R_0^s$, and the Khasminskii criterion (uniform ellipticity on a bounded domain plus a drift condition outside it) gives positive recurrence and ergodicity. For clearance, the naive functional $\ln(y + z)$ loses the deterministic threshold; weighting by $\alpha$ and choosing $\alpha$ so that the two growth rates of the infected subsystem balance recovers $\lambda_{\max}(J)$ when the noise vanishes. The convex dependence of the escape rate on $x$ prevents substituting $\bar x$ for $x$; instead exact occupation identities for $x + y$, derived from Itô's formula for $N$ and $N^2$, bound the long-run averages of $x$ and $x^2$, and the bound on $\langle x^2\rangle$ is attained under clearance, showing it cannot be improved. Exclusivity follows by multiplying the two inequalities that $\Lambda_{\mathrm{ext}} < 0$ imposes on the optimal weight, which eliminates $\alpha$ and yields $R_0^s < 1$.

## Sources

- Abdallah Alsammani, "Stochastic Dynamics of Hepatitis B Virus Infection: Extinction, Persistence, and Ergodicity", arXiv:2308.05819 (2023), Section 2 (deterministic model, $R_0$, $\lambda_{\max}(J)$; stochastic system), Section 4 (Theorem 4.1, Lemma 4.1), Section 5 (hypotheses (H1)–(H3), Lemmas 5.1–5.4, Theorem 5.1, Proposition 5.1, Theorem 5.2, Corollary 5.1), Section 6 ($R_0^s$, Theorem 6.1, Proposition 6.1). <https://doi.org/10.48550/arXiv.2308.05819>
