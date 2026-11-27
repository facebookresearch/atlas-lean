# Equal per-cell variance, equal precision iff equal donor variance

Let $\delta$ be a finite nonempty set of $D$ donors and $\kappa$ a finite set of $m \ge 2$ cell
slots. Let $Y$ be a [random-intercept model](is-random-intercept.md) with variances
$(\sigma_b^2, \sigma_e^2)$ under a finite measure $\mu$ on $\Omega$, and $Y'$ one with variances
$(\sigma_b'^2, \sigma_e'^2)$ under a finite measure $\mu'$ on $\Omega'$, with the same per-cell
variance $\sigma_b^2 + \sigma_e^2 = \sigma_b'^2 + \sigma_e'^2$. Then their
[cell-level means](cell-mean.md) have the same variance,
$\mathrm{Var}_\mu \bar Y = \mathrm{Var}_{\mu'} \bar Y'$, if and only if $\sigma_b^2 = \sigma_b'^2$.
Within the random-intercept family the per-cell variance does not determine the variance of the
cell-level mean; its split into donor and residual variance does.
