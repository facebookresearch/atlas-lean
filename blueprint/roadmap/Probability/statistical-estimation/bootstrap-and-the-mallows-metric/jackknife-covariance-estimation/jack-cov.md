# Delete-one jackknife covariance

For block vectors $z_1, \dots, z_B \in \mathbb{R}^n$ with mean $\bar z$ and leave-one-out means $\bar z_{(-b)}$, the delete-one jackknife covariance is

$$V_{\mathrm{jack}} = \frac{B-1}{B}\sum_b(\bar z_{(-b)} - \bar z)(\bar z_{(-b)} - \bar z)^\top.$$

Real division and inversion use $x/0 = 0$ and $0^{-1} = 0$.
