# Leave-one-out deviations of block means

For $B$ block vectors $z_1, \dots, z_B \in \mathbb{R}^n$, write $\bar z = \frac1B\sum_b z_b$, $\bar z_{(-b)} = \frac1{B-1}\sum_{c \ne b}z_c$ for the leave-one-out means, and $V_{\mathrm{jack}} = \frac{B-1}{B}\sum_b(\bar z_{(-b)} - \bar z)(\bar z_{(-b)} - \bar z)^\top$ for the delete-one jackknife covariance. If $B \ge 2$, then for every block $b$, $\bar z_{(-b)} - \bar z = -\frac{1}{B-1}(z_b - \bar z)$.
