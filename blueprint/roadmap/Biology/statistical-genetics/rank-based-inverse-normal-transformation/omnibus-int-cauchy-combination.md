# Omnibus INT test by Cauchy combination

Let $p_D$ and $p_I$ be the $p$-values of the [direct and indirect INT tests](direct-and-indirect-int-score-tests.md) of the same null hypothesis $H_0: \beta_G = 0$. With $F_C^{-1}(u) = \tan\big(\pi(u - \tfrac12)\big)$ the standard Cauchy quantile function, the omnibus INT statistic is

$$T_O = -\frac12\Big[F_C^{-1}(p_D) + F_C^{-1}(p_I)\Big] = \frac12\Big[\tan\big(\pi(\tfrac12 - p_D)\big) + \tan\big(\pi(\tfrac12 - p_I)\big)\Big],$$

with $p$-value

$$p_O = \Pr(T_O > t_O) = \frac12 - \frac{1}{\pi}\arctan(t_O)$$

computed from the standard Cauchy law.

Under $H_0$ each of $p_D$, $p_I$ is uniform, so each term $\tan(\pi(\tfrac12 - p))$ is standard Cauchy. If the two terms were independent, $T_O$ would be exactly standard Cauchy, since an average of independent standard Cauchy variables is standard Cauchy; for the positively dependent D-INT and I-INT $p$-values the Cauchy reference is the approximation of Liu and Xie for Cauchy combinations of dependent tests, accurate in the tail. In the paper's simulations D-INT and I-INT both controlled type I error but neither was uniformly more powerful, which motivates combining them.

## Depends on

- [Direct and indirect INT association tests](direct-and-indirect-int-score-tests.md)

## Expansion

If $U$ is uniform on $(0,1)$ then $\tan(\pi(\tfrac12 - U))$ has distribution function $\tfrac12 + \tfrac1\pi\arctan(t)$, the standard Cauchy law, and its upper tail at $t$ is $\tfrac12 - \tfrac1\pi\arctan(t)$. The Cauchy family is stable: for independent standard Cauchy $C_1, C_2$ and weights $w_1 + w_2 = 1$, $w_1C_1 + w_2C_2$ is standard Cauchy. Small $p$-values map to large positive terms, so $T_O$ is dominated by the more significant component.

## Sources

- Z. R. McCaw, J. M. Lane, R. Saxena, S. Redline and X. Lin, "Operating characteristics of the rank-based inverse normal transformation for quantitative trait analysis in genome-wide association studies", Biometrics 76 (2020), <https://doi.org/10.1111/biom.13214> (PMC8643141); preprint version <https://doi.org/10.1101/635706>, section 2.6, Equation (15).
