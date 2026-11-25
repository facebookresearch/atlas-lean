# The independence model reproduces the naive formula

Let $\delta$ be a finite nonempty set of $D$ donors and $\kappa$ a finite nonempty set of $m$ cell
slots, so that every donor has $m \ge 1$ cells $i = (d, c)$. Let $\mu$ be a finite measure on
$\Omega$, let $\sigma_b^2$ and $\sigma_e^2$ be real, and let the cell values form a
[random-intercept model](is-random-intercept.md) under $\mu$ with donor variance $0$ and residual
variance $\sigma_b^2 + \sigma_e^2$ (which is then nonnegative). Then the
[cell-level mean](cell-mean.md) $\bar Y$ has variance exactly the [naive variance](naive-var.md)
$V_{\mathrm{naive}}(D, m) = (\sigma_b^2 + \sigma_e^2) / (D m)$.
