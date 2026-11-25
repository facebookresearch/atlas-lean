# Row sums of the random-intercept kernel

Let $\delta$ be a finite set of $D$ donors and $\kappa$ a finite set of $m$ cell slots, so that
every donor has $m$ cells $i = (d, c)$ (a balanced design). For real $\sigma_b^2$, $\sigma_e^2$ and
every cell $i$, the row sum of the [random-intercept kernel](ri-cov.md) is

$$\sum_{j \in \delta \times \kappa} k(i, j) = m\, \sigma_b^2 + \sigma_e^2.$$
