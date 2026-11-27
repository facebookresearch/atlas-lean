# Mode-based bias correction and asymptotic FDR control for CLR regression

In the CLR regression setting, let $\tilde\alpha_i$ be the OLS coefficient of $u_s$ for taxon $i$, $\hat\sigma_i^2$ the residual variance estimate with $n - d - 2$ degrees of freedom, and $\hat\rho$ the $(1,1)$ entry of $(n^{-1}\sum_s z_s z_s^\top)^{-1}$. Assume most taxa are not differential, so the values $\sqrt n\,\tilde\alpha_i$ cluster at $-\sqrt n\,\bar\alpha$. Estimate the bias by the kernel mode

$$\tilde\alpha = -\frac{1}{\sqrt n}\,\arg\max_{x \in \mathbb{R}} \frac{1}{mh}\sum_{i=1}^m K\!\left(\frac{x - \sqrt n\,\tilde\alpha_i}{h}\right),$$

with $K \ge 0$ even, $\int K = 1$ and bandwidth $h$, set $\hat\alpha_i = \tilde\alpha_i + \tilde\alpha$, $T_i = \sqrt n\,\hat\alpha_i / \sqrt{\hat\rho\,\hat\sigma_i^2}$, $p_i = 2F_{n-d-2}(-|T_i|)$ with $F_\nu$ the Student $t$ distribution function, and apply the Benjamini–Hochberg procedure at level $q$, i.e. reject at the threshold $t^*$, the smallest $t$ with

$$\widehat{\mathrm{FDP}}(t) = \frac{2m\,F_{n-d-2}(-t)}{\sum_{i=1}^m \mathbb{1}\{\sqrt n\,|\hat\alpha_i| / \sqrt{\hat\rho\,\hat\sigma_i^2} > t\}} \le q.$$

**Theorem.** Suppose: the $z_s$ are i.i.d. with sub-Gaussian entries and $\lambda_{\min}(\mathbb{E} z_s z_s^\top) > C$; the $\sigma_i$ are i.i.d. with $C_1 < \sigma_i < C_2$ almost surely; $\varepsilon_{is}/\sigma_i$ are i.i.d. $N(0,1)$; the $\alpha_i$ are i.i.d.; all these families are mutually independent; for large $n$ the density of $\sqrt n\,\alpha_i + \sqrt\rho\,\varepsilon_{is}$ ($\rho$ the $(1,1)$ entry of $(\mathbb{E} z_s z_s^\top)^{-1}$) has a unique, uniformly well-separated mode at $0$; the Fourier transform of $K$ is absolutely integrable; $h \to 0$ and $m h^2 \to \infty$; $m = o(e^{Cn})$; and a threshold $t_0$ exists at which the $t$-tail $2F_{n-d-2}(-t_0)$ is at most $q$ times the limiting rejection probability. Then, as $m, n \to \infty$,

$$\limsup_{m, n \to \infty} \mathrm{FDR}_{m,n}(t^*) \le q.$$

## Depends on

- [Compositional bias of CLR regression coefficients](clr-regression-coefficient-bias.md)
- [Benjamini–Hochberg rejection set](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)

## Expansion

Since most $\alpha_i = 0$, the empirical distribution of $\sqrt n\,\tilde\alpha_i$ is a location mixture whose dominant component is centered at $-\sqrt n\,\bar\alpha$; the unique-mode condition makes the kernel mode consistent, giving $\sqrt n(\tilde\alpha - \bar\alpha) = o_{\mathbb{P}}(1)$. The variance of $\tilde\alpha$ is of smaller order than that of $\tilde\alpha_i$, so $\hat\rho\hat\sigma_i^2/n$ estimates $\operatorname{var}(\hat\alpha_i)$, the statistics $T_i$ are asymptotically normal, and the BH argument goes through with the estimated null proportion bounded by one. The condition $m = o(e^{Cn})$ lets the number of taxa grow exponentially in the sample size.

## Sources

- H. Zhou, K. He, J. Chen, X. Zhang, *LinDA: linear models for differential abundance analysis of microbiome compositional data*, Genome Biology 23 (2022), 95, Methods, equations (6) and (7) and Theorem 1. <https://doi.org/10.1186/s13059-022-02655-5> (PMCID: PMC9012043)
