# The semi-discrete stochastic SIS scheme preserves almost-sure exponential extinction

**Setting.** Consider the stochastic SIS model

$$
dI_t = \Big(\eta I_t - \frac{\beta}{K} I_t^2\Big)dt + \sigma (K-I_t)I_t\, dW_t, \qquad \eta = \beta - b - \gamma,\ I_0\in(0,K),
$$

and its domain-preserving semi-discrete approximation $\hat Y_n = K\hat X_n/(1+\hat X_n)$, where

$$
\hat X_{n+1} = \hat X_n \exp\Big\{\Big(\eta - (b+\gamma)\hat X_n + \frac{\sigma^2K^2\hat X_n}{1+\hat X_n} - \tfrac12\sigma^2K^2\Big)\Delta + \sigma K\,\Delta W_n\Big\},\qquad \hat X_0 = \frac{I_0}{K-I_0}.
$$

**Exact process (Gray et al.).** Let $\mathcal R_0^D = \beta/(b+\gamma)$ be the deterministic reproduction number of the drift $\eta I - (\beta/K)I^2$. If the stochastic reproduction number $\mathcal R_0^S = \mathcal R_0^D - \frac{\sigma^2K^2}{2(b+\gamma)} < 1$ and $\sigma^2 \le \beta/K^2$, then for every $I_0\in(0,K)$, almost surely

$$
\limsup_{t\to\infty} \frac1t \ln I_t \le \beta - b - \gamma - \tfrac12 \sigma^2K^2 < 0 .
$$

**Theorem (numerical extinction).** Under the same hypotheses and, in addition, $\sigma^2K^2 \le b+\gamma$, for every step size $0<\Delta<1$, almost surely

$$
\limsup_{n\Delta\to\infty} \frac{1}{n\Delta} \ln \hat Y_n \le \beta - b - \gamma - \tfrac12 \sigma^2K^2 < 0,
$$

so the scheme reproduces the exponential die-out of the disease with the same rate bound, for every step size.

## Proof sketch

The hypothesis $\mathcal R_0^S < 1$ is exactly $\beta - b - \gamma - \tfrac12\sigma^2K^2 < 0$, the sign of the stated rate. (The source writes $\mathcal R_0^D = \beta/(K(b+\gamma))$, which belongs to the unscaled incidence; with it the hypothesis would not imply a negative rate, e.g. $K = 10$, $\beta = 5$, $b + \gamma = 1$, $\sigma^2 = 0.01$.)

Take logarithms in the scheme. Since $\hat X_n/(1+\hat X_n) \le \hat X_n$, the drift in the exponent is at most $\eta - \frac12\sigma^2K^2 + (\sigma^2K^2 - (b+\gamma))\hat X_n$, and the extra hypothesis $\sigma^2K^2\le b+\gamma$ makes the last term nonpositive. Telescoping gives $\ln \hat X_n \le \ln \hat X_0 + n\Delta(\eta - \frac12\sigma^2K^2) + \sigma K W_{n\Delta}$, and the law of the iterated logarithm kills $W_{n\Delta}/(n\Delta)$. Finally $\ln \hat Y_n \le \ln K + \ln \hat X_n$. The step-size independence contrasts with Euler–Maruyama, whose iterates can leave $(0,K)$ and whose stability needs small $\Delta$.

## Depends on

- [Semi-discrete exponential scheme for the stochastic SIS model converges strongly with order 1](semi-discrete-exponential-scheme-for-the-stochastic-sis-model.md)

## Sources

- Yiannis Kiouvrekis and Ioannis S. Stamatiou, "Domain preserving and strongly converging explicit scheme for the stochastic SIS epidemic model", *Journal of Computational and Applied Mathematics* 456 (2025), 116219, <https://doi.org/10.1016/j.cam.2024.116219>. Preprint version: arXiv:2307.14404 (2023), Theorem 2 (quoting Gray et al. 2011, Theorem 4.1) and Theorem 3, proved in Section 3, <https://doi.org/10.48550/arXiv.2307.14404>.
