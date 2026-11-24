# The replicate formula is exact for pseudobulk

Let $\delta$ be a finite nonempty set of $D$ donors and $\kappa$ a finite nonempty set of $m$ cell
slots, so that every donor has $m \ge 1$ cells $i = (d, c)$. Let $\mu$ be a finite measure on
$\Omega$ and let the cell values $Y_i : \Omega \to \mathbb{R}$ form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $\sigma_b^2$ and
residual variance $\sigma_e^2$, variances being taken with respect to $\mu$. Then the
[mean of the pseudobulk values](pseudobulk-mean.md) has variance

$$
\mathrm{Var}\, \bar Y_{\mathrm{pb}} = \frac{\sigma_b^2 + \sigma_e^2 / m}{D}
= \frac{\sigma_b^2}{D} + \frac{\sigma_e^2}{D m}:
$$

the [variance of a pseudobulk value](covariance-pseudobulk.md) divided by the number of donors, as
for $D$ uncorrelated replicates, and equal to the [true variance](true-var.md) of the cell-level
mean.
