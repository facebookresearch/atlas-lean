# Delete-one-block jackknife covariance of a mean

For $B \ge 2$ vectors $z_1, \dots, z_B \in \mathbb R^k$, with mean $\bar z = \frac1B \sum_b z_b$ and leave-one-out means $\bar z_{(-b)} = \frac{1}{B - 1}\sum_{c \ne b} z_c$, the
delete-one-block jackknife covariance is

$$V_{\mathrm{jack}} = \frac{B - 1}{B} \sum_{b=1}^B (\bar z_{(-b)} - \bar z)(\bar z_{(-b)} - \bar z)^\top = \frac{1}{B(B - 1)} \sum_{b=1}^B (z_b - \bar z)(z_b - \bar z)^\top,$$

because $\bar z_{(-b)} - \bar z = (\bar z - z_b)/(B - 1)$. So $B\, V_{\mathrm{jack}}$ is the sample covariance of the blocks with divisor $B - 1$; it is $0$ exactly when all
$z_b$ are equal. This is an algebraic identity; it says nothing about consistency under dependence between blocks.

## Sources

- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998) (jackknife). The identity is derived above.
