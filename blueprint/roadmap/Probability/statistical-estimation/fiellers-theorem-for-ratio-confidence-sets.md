# Fieller's confidence sets for a ratio of means

Let $(a, b)$ be bivariate normal with mean $(\alpha, \beta)$ and known, positive definite covariance matrix with entries $v_{aa}, v_{ab}, v_{bb}$, and let $\theta_0 = \alpha/\beta$ with $\beta \ne 0$ be the true ratio. For every real $t$, $a - t b$ is normal with mean $\alpha - t\beta$ and variance $v(t) = v_{aa} - 2t v_{ab} + t^2 v_{bb}$, and $v(t) > 0$ because the covariance matrix is positive definite. At $t = \theta_0$ the mean is $\alpha - \theta_0\beta = 0$, so $(a - \theta_0 b)^2/v(\theta_0)$ has the $\chi^2_1$ law, and the Fieller set

$$C = \{t : (a - t b)^2 \le z^2\, v(t)\},$$

with $z$ the upper $\alpha/2$ normal quantile, contains $\theta_0$ with probability exactly $1 - \alpha$, for every value of the parameters with $\beta \ne 0$. $C$ is the solution set of a quadratic inequality in $t$ with leading coefficient $b^2 - z^2 v_{bb}$: if this is positive, $C$ is a bounded interval; if it is negative, $C$ is the complement of a bounded interval when the discriminant is positive and the whole real line otherwise. In Fieller's (1954) setting the covariance is $\sigma^2(\nu_{11}, \nu_{12}, \nu_{22})$ with $\nu$ known and $\sigma^2$ estimated by $s^2$ on $r$ degrees of freedom; with $t_{r,\alpha}$ in place of $z$ and $g = t_{r,\alpha}^2 s^2 \nu_{22}/b^2$, the endpoints are

$$\frac{1}{1 - g}\Bigl[\frac{a}{b} - \frac{g \nu_{12}}{\nu_{22}} \mp \frac{t_{r,\alpha}\, s}{b}\sqrt{\nu_{11} - 2\frac{a}{b}\nu_{12} + \frac{a^2}{b^2}\nu_{22} - g\Bigl(\nu_{11} - \frac{\nu_{12}^2}{\nu_{22}}\Bigr)}\Bigr],$$

the interval is infinite as $g$ approaches $1$, and for $g > 1$ the set is exclusive, the complement of the interval between the two values (Fieller's theorem, Wikipedia).

## Expansion

1. The model and the pivotal quantity $(a - \theta b)^2/v(\theta)$, and exact coverage.
2. The shapes of $C$ according to the leading coefficient and the discriminant, including the degenerate boundary cases.
3. The version with estimated $\sigma^2$, the $t$ pivot, and the endpoint formula in terms of $g$.

## Sources

- Fieller's theorem, Wikipedia, section on the approximate confidence interval. <https://en.wikipedia.org/wiki/Fieller%27s_theorem>
- Original result: E. C. Fieller, Some problems in interval estimation, J. Roy. Statist. Soc. Ser. B 16 (1954), 175–185. <https://doi.org/10.1111/j.2517-6161.1954.tb00159.x> The interval with estimated variance follows Fieller's theorem, Wikipedia.
