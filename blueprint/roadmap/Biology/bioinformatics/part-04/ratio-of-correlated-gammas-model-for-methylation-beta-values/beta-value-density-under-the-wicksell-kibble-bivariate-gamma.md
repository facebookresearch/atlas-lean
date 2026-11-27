# Beta-value density under the Wicksell–Kibble bivariate gamma

At a CpG site a methylation array reports a methylated intensity $M > 0$ and an unmethylated intensity $U > 0$, and the beta value is $b = M/(M+U) \in (0,1)$. Suppose $(M,U)$ has the Wicksell–Kibble bivariate gamma density with common shape $\alpha > 0$, rates $\lambda_m, \lambda_u > 0$ and correlation parameter $0 < \rho < 1$:

$$f_{M,U}(m,u) = \frac{(\lambda_m\lambda_u)^{\alpha}}{(1-\rho)\,\Gamma(\alpha)}\left(\frac{mu}{\rho\lambda_m\lambda_u}\right)^{\frac{\alpha-1}{2}} \exp\!\left(-\frac{\lambda_m m + \lambda_u u}{1-\rho}\right) I_{\alpha-1}\!\left(\frac{2\sqrt{\rho\lambda_m\lambda_u m u}}{1-\rho}\right),$$

where $I_{\alpha-1}$ is the modified Bessel function of the first kind. Its marginals are $M \sim \mathrm{Gamma}(\alpha, \lambda_m)$ and $U \sim \mathrm{Gamma}(\alpha, \lambda_u)$ and the Pearson correlation of $M$ and $U$ is $\rho$. Then $b$ has density, for $0 < b < 1$,

$$f_b(b) = \frac{\Gamma(2\alpha)}{\Gamma(\alpha)^2}\,(\lambda_m\lambda_u)^{\alpha}(1-\rho)^{\alpha}\,[b(1-b)]^{\alpha-1}\,\frac{L(b)}{\bigl(L(b)^2 - 4\rho\lambda_m\lambda_u\, b(1-b)\bigr)^{\alpha+1/2}}, \qquad L(b) = \lambda_m b + \lambda_u(1-b).$$

It depends on the rates only through $\theta = \lambda_m/\lambda_u = \mathrm{E}(U)/\mathrm{E}(M)$: dividing numerator and denominator by $\lambda_u^{2\alpha}$ gives $f_b(b) = \frac{\Gamma(2\alpha)}{\Gamma(\alpha)^2}\theta^{\alpha}(1-\rho)^{\alpha}[b(1-b)]^{\alpha-1}((\theta-1)b+1)\big/\bigl(((\theta-1)b+1)^2 - 4\rho\theta b(1-b)\bigr)^{\alpha+1/2}$. Letting $\rho \to 0$ recovers the ratio of independent gammas with a common shape, and with $\theta = 1$ as well the $\mathrm{Beta}(\alpha,\alpha)$ law, the case implicitly assumed by beta regression.

## Proof depends on

- [Real moments of the gamma density](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/lintegral-gamma-pdf-mul-rpow.md)

## Expansion

Expand the Bessel function, $I_{\nu}(z) = \sum_{k \ge 0} (z/2)^{2k+\nu}/(k!\,\Gamma(k+\nu+1))$, so that $f_{M,U}$ becomes a series in $(mu)^{k+\alpha-1}e^{-(\lambda_m m+\lambda_u u)/(1-\rho)}$. The density of $b$ is $\int_0^\infty s\, f_{M,U}(sb, s(1-b))\,ds$; term by term the $s$-integral is $\Gamma(2k+2\alpha)(1-\rho)^{2k+2\alpha}/L(b)^{2k+2\alpha}$, which leaves the factor $(1-\rho)^{\alpha}$. The duplication formula $\Gamma(2k+2\alpha) = 2^{2k+2\alpha-1}\Gamma(k+\alpha)\Gamma(k+\alpha+\tfrac12)/\sqrt{\pi}$ turns the remaining sum into the binomial series $\sum_k \Gamma(k+\alpha+\frac12)(4x)^k/k! = \Gamma(\alpha+\frac12)(1-4x)^{-\alpha-1/2}$ with $x = \rho\lambda_m\lambda_u b(1-b)/L(b)^2 < 1/4$, which gives the closed form.

## Sources

- L. Weinhold, S. Wahl, S. Pechlivanis, P. Hoffmann and M. Schmid, "A statistical model for the analysis of beta values in DNA methylation studies", BMC Bioinformatics 17 (2016), 480, <https://doi.org/10.1186/s12859-016-1347-4>, PMCID PMC5120494. Proposition 1 and Eqs. (6)–(9); the reparametrization in $\theta$ is Proposition 2, Eq. (10).
