# Tensor product of trade-off functions

For trade-off functions $f = T(P, Q)$ and $g = T(P', Q')$, their **tensor product** is

$$
f \otimes g = T\big(P \times P',\; Q \times Q'\big).
$$

This is well defined: the right side depends only on $f$ and $g$, not on the representing pairs. The operation is commutative and associative, has $\mathrm{Id}(\alpha) = 1 - \alpha$ as identity, is monotone ($f \ge f'$ implies $f \otimes g \ge f' \otimes g$), and satisfies $G_{\mu_1} \otimes G_{\mu_2} = G_{\sqrt{\mu_1^2 + \mu_2^2}}$.

## Depends on

- [Trade-off functions of pairs of distributions](trade-off-function.md)
- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
