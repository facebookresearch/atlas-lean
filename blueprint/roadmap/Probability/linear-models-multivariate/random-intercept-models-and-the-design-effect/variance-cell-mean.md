# Variance of the cell-level mean

Let $\delta$ be a finite nonempty set of $D$ donors and $\kappa$ a finite nonempty set of $m$ cell
slots, so that every donor has $m \ge 1$ cells $i = (d, c)$. Let $\mu$ be a finite measure on
$\Omega$ and let the cell values $Y_i : \Omega \to \mathbb{R}$ form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $\sigma_b^2$ and
residual variance $\sigma_e^2$, variances being taken with respect to $\mu$. Then the
[cell-level mean](cell-mean.md) $\bar Y$ has variance

$$\mathrm{Var}\, \bar Y = \frac{\sigma_b^2}{D} + \frac{\sigma_e^2}{D m},$$

the [true variance](true-var.md) $V_{\mathrm{true}}(D, m)$.
