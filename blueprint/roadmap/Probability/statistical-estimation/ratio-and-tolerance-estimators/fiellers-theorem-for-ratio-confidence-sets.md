# Fieller's confidence sets for a ratio of means

Let $(a, b)$ be bivariate normal with mean $(\mu_a, \mu_b)$ and known, positive definite covariance matrix with entries $v_{aa}, v_{ab}, v_{bb}$, and let $\theta_0 = \mu_a/\mu_b$ with $\mu_b \ne 0$ be the true ratio. Fix a significance level $\alpha \in (0, 1)$ and let $z = z_{1-\alpha/2}$ be the upper $\alpha/2$ quantile of the standard normal law, $P(|N(0, 1)| > z) = \alpha$. For every real $\theta$, $a - \theta b$ is normal with mean $\mu_a - \theta\mu_b$ and variance $v(\theta) = v_{aa} - 2\theta v_{ab} + \theta^2 v_{bb} > 0$. At $\theta = \theta_0$ the mean is $0$, so $(a - \theta_0 b)^2/v(\theta_0)$ has the $\chi^2_1$ law, and the Fieller set

$$C = \{\theta \in \mathbb{R} : (a - \theta b)^2 \le z^2\, v(\theta)\}$$

contains $\theta_0$ with probability exactly $1 - \alpha$, for every value of the parameters with $\mu_b \ne 0$.

Shape of $C$. The defining inequality is $q(\theta) \le 0$ with

$$q(\theta) = (b^2 - z^2 v_{bb})\,\theta^2 - 2(ab - z^2 v_{ab})\,\theta + (a^2 - z^2 v_{aa}),$$

and if $b \ne 0$, which holds almost surely, then $q(a/b) = -z^2 v(a/b) < 0$, so $a/b \in C$. Hence: if $b^2 - z^2 v_{bb} > 0$, $C$ is a bounded closed interval containing $a/b$; if $b^2 - z^2 v_{bb} < 0$, $C$ is the complement of a bounded open interval when the discriminant of $q$ is positive and all of $\mathbb{R}$ otherwise; and if $b^2 - z^2 v_{bb} = 0$, $q$ is affine, so $C$ is a closed half-line containing $a/b$ when $ab \ne z^2 v_{ab}$ and all of $\mathbb{R}$ when $ab = z^2 v_{ab}$.

Estimated variance. In Fieller's (1954) setting the covariance is $\sigma^2(\nu_{11}, \nu_{12}, \nu_{22})$ with $\nu$ known and positive definite, and $\sigma^2$ is estimated by $s^2 > 0$ with $r s^2/\sigma^2 \sim \chi^2_r$ independent of $(a, b)$. With $\nu(\theta) = \nu_{11} - 2\theta\nu_{12} + \theta^2\nu_{22}$ and $t = t_{r,1-\alpha/2}$ the upper $\alpha/2$ quantile of the Student law $t_r$, $(a - \theta_0 b)^2/(s^2\nu(\theta_0))$ is the square of a $t_r$ variable, so the set

$$C_s = \{\theta \in \mathbb{R} : (a - \theta b)^2 \le t^2 s^2\, \nu(\theta)\}$$

contains $\theta_0$ with probability exactly $1 - \alpha$. For every $(a, b)$ its shape is that of the classification above with $z^2 v$ replaced by $t^2 s^2 \nu$, read off the defining inequality, whose leading coefficient is $b^2 - t^2 s^2\nu_{22}$; in particular $C_s$ is never empty when $b \ne 0$, and when $b = 0$ the leading coefficient is negative. Fieller's endpoint formula is a special case. Suppose $b \ne 0$, let $g = t^2 s^2 \nu_{22}/b^2$, so that the leading coefficient is $b^2(1 - g)$, and let

$$D = \nu_{11} - 2\frac{a}{b}\nu_{12} + \frac{a^2}{b^2}\nu_{22} - g\Bigl(\nu_{11} - \frac{\nu_{12}^2}{\nu_{22}}\Bigr).$$

If $g \ne 1$ and $D \ge 0$, the roots of the defining quadratic are

$$\frac{1}{1 - g}\Bigl[\frac{a}{b} - \frac{g \nu_{12}}{\nu_{22}} \mp \frac{t\, s}{b}\sqrt{D}\Bigr]$$

(Fieller's theorem, Wikipedia), and $C_s$ is the closed interval between them if $g < 1$ and the complement of the open interval between them if $g > 1$. For $g < 1$ the radicand is always positive, since the quadratic is negative at $a/b$ and has positive leading coefficient. For $g > 1$ and $D < 0$, $C_s = \mathbb{R}$. For $g = 1$ the formula does not apply; the defining inequality is then affine in $\theta$, $-2(ab - t^2 s^2\nu_{12})\,\theta + (a^2 - t^2 s^2\nu_{11}) \le 0$, and since it holds strictly at $\theta = a/b$, $C_s$ is a closed half-line containing $a/b$ when $ab \ne t^2 s^2\nu_{12}$ and all of $\mathbb{R}$ otherwise.

## Expansion

1. The model and the pivotal quantity $(a - \theta b)^2/v(\theta)$, and exact coverage.
2. The shapes of $C$ according to the sign of the leading coefficient and the discriminant, using $q(a/b) < 0$, including the affine case of zero leading coefficient.
3. The version with estimated $\sigma^2$: the $t$ pivot and its exact coverage, the endpoint formula for $b \ne 0$, $g \ne 1$ and $D \ge 0$, the case $g > 1$, $D < 0$, and the affine case $g = 1$.

## Sources

- Fieller's theorem, Wikipedia, section on the approximate confidence interval. <https://en.wikipedia.org/wiki/Fieller%27s_theorem>
- Original result: E. C. Fieller, Some problems in interval estimation, J. Roy. Statist. Soc. Ser. B 16 (1954), 175–185. <https://doi.org/10.1111/j.2517-6161.1954.tb00159.x> The interval with estimated variance follows Fieller's theorem, Wikipedia.
