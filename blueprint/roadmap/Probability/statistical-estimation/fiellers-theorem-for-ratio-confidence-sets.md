# Fieller's confidence sets for a ratio of means

Let $(a, b)$ be bivariate normal with mean $(\alpha, \beta)$ and known covariance matrix with entries $v_{aa}, v_{ab}, v_{bb}$, and let $\theta = \alpha/\beta$ with $\beta \ne 0$. For each $\theta$, $a - \theta b$ is normal with mean $0$ and variance $v(\theta) = v_{aa} - 2\theta v_{ab} + \theta^2 v_{bb}$, so $(a - \theta b)^2/v(\theta)$ is $\chi^2_1$ at the true $\theta$ and the Fieller set
$$C = \{\theta : (a - \theta b)^2 \le z^2\, v(\theta)\},$$
with $z$ the upper $\alpha/2$ normal quantile, has coverage exactly $1 - \alpha$ for every value of the parameters. $C$ is the solution set of a quadratic inequality in $\theta$ with leading coefficient $b^2 - z^2 v_{bb}$: if this is positive, $C$ is a bounded interval; if it is negative, $C$ is the complement of a bounded interval when the discriminant is positive and the whole real line otherwise. In Fieller's (1954) setting the covariance is $\sigma^2(\nu_{11}, \nu_{12}, \nu_{22})$ with $\nu$ known and $\sigma^2$ estimated by $s^2$ on $r$ degrees of freedom; with $t_{r,\alpha}$ in place of $z$ and $g = t_{r,\alpha}^2 s^2 \nu_{22}/b^2$, the endpoints are
$$\frac{1}{1 - g}\Bigl[\frac{a}{b} - \frac{g \nu_{12}}{\nu_{22}} \mp \frac{t_{r,\alpha}\, s}{b}\sqrt{\nu_{11} - 2\frac{a}{b}\nu_{12} + \frac{a^2}{b^2}\nu_{22} - g\Bigl(\nu_{11} - \frac{\nu_{12}^2}{\nu_{22}}\Bigr)}\Bigr],$$
the interval is infinite as $g$ approaches $1$, and for $g > 1$ the set is exclusive, the complement of the interval between the two values (Fieller's theorem, Wikipedia).

## Expansion

1. The model and the pivotal quantity $(a - \theta b)^2/v(\theta)$, and exact coverage.
2. The shapes of $C$ according to the leading coefficient and the discriminant, including the degenerate boundary cases.
3. The version with estimated $\sigma^2$, the $t$ pivot, and the endpoint formula in terms of $g$.

## Sources

- Fieller's theorem, Wikipedia, section on the approximate confidence interval. <https://en.wikipedia.org/wiki/Fieller%27s_theorem>
- Original result: E. C. Fieller, Some problems in interval estimation, J. Roy. Statist. Soc. Ser. B 16 (1954), 175–185. <https://doi.org/10.1111/j.2517-6161.1954.tb00159.x> The interval with estimated variance follows Fieller's theorem, Wikipedia.
