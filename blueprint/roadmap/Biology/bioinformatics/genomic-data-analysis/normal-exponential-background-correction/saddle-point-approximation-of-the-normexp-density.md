# Saddle-point approximation of the normal–exponential density

Let $X = B + S$ with $B \sim \mathcal{N}(\mu, \sigma^2)$ and $S$ exponential with mean $\alpha$, independent, so that $K(\theta) = \mu\theta + \tfrac{1}{2}\sigma^2\theta^2 - \log(1 - \alpha\theta)$ for $\theta < 1/\alpha$, with derivatives

$$K'(\theta) = \mu + \sigma^2\theta + \frac{\alpha}{1 - \alpha\theta}, \qquad K''(\theta) = \sigma^2 + \frac{\alpha^2}{(1 - \alpha\theta)^2}, \qquad K^{(r)}(\theta) = \frac{(r-1)!\, \alpha^r}{(1 - \alpha\theta)^r} \ (r \ge 3).$$

**Saddle point.** For each observation $x$ the equation $K'(\hat\theta) = x$ has exactly one solution with $\hat\theta < 1/\alpha$, namely, with $y = x - \mu$,

$$\hat\theta = \frac{(\sigma^2 + \alpha y) - \sqrt{(\sigma^2 - \alpha y)^2 + 4 \sigma^2 \alpha^2}}{2 \sigma^2 \alpha} .$$

**Approximation.** The second-order saddle-point (tilted Edgeworth) approximation of the density is

$$\hat f_X(x) = \frac{\exp\big(K(\hat\theta) - \hat\theta x\big)}{\sqrt{2\pi K''(\hat\theta)}} \left(1 + \frac{\rho_4}{8} - \frac{5 \rho_3^2}{24}\right), \qquad \rho_r = \frac{K^{(r)}(\hat\theta)}{K''(\hat\theta)^{r/2}} ,$$

and its logarithm is a closed-form expression, which retains good relative accuracy far into the tails where the exact density suffers from cancellation.

**Estimation.** Maximizing $\sum_i \log \hat f_X(x_i)$ over $(\mu, \log\sigma^2, \log\alpha)$ gives saddle-point estimates; using them as starting values for maximizing the exact likelihood gives a reliable maximum likelihood estimator, which is more accurate than heuristic (mode- or quantile-partition) estimators.

## Depends on

- [Normal–exponential convolution density and signal posterior mean](normexp-convolution-density-and-signal-posterior-mean.md)

## Expansion

Rewriting $K'(\theta) = x$ as $\sigma^2\alpha\theta^2 - (\sigma^2 + \alpha y)\theta + (y - \alpha) = 0$ gives a quadratic with discriminant $(\sigma^2 - \alpha y)^2 + 4\sigma^2\alpha^2 > 0$. The quadratic equals $-\alpha < 0$ at $\theta = 1/\alpha$, so $1/\alpha$ lies strictly between its roots and only the smaller root is admissible. Since $K''> 0$, $K'$ is increasing on $(-\infty, 1/\alpha)$ with range $\mathbb{R}$, confirming uniqueness. The tilted density $f_X(x) e^{\theta x - K(\theta)}$ is a linear exponential family in $\theta$; choosing $\theta = \hat\theta$ centres it at $x$, where its Edgeworth expansion is most accurate, and undoing the tilt yields the formula. Evaluating the closed-form root naively still suffers cancellation for some $(\sigma, \alpha)$, which is avoided by an algebraically equivalent rearrangement or by globally convergent iteration.

## Sources

- J. D. Silver, M. E. Ritchie and G. K. Smyth, "Microarray background correction: maximum likelihood estimation for the normal–exponential convolution", Biostatistics 10 (2009), Sections 2.2–2.3, <https://doi.org/10.1093/biostatistics/kxn042> (PMC2648902).
