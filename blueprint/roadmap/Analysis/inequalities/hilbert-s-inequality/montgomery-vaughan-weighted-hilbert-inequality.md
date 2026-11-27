# Montgomery–Vaughan weighted Hilbert inequality

There is an absolute constant $C>0$ with the following property. Let $(\lambda_r)_{r\in I}$ be distinct real frequencies indexed by a finite set. Let the real weights $\delta_r$ be positive and satisfy $\delta_r\le |\lambda_r-\lambda_s|$ whenever $s\ne r$. For any complex families $(x_r)$ and $(z_r)$,

$$
\left|\sum_{r\ne s}\frac{x_r\overline{z_s}}{\lambda_r-\lambda_s}\right|
\le C\left(\sum_r\frac{|x_r|^2}{\delta_r}\right)^{1/2}
     \left(\sum_s\frac{|z_s|^2}{\delta_s}\right)^{1/2}.
$$

The sum is over ordered distinct pairs. The inequality uses local frequency spacing, not the kernel $1/(m+n+2)$ of the classical finite Hilbert inequality.

## Expansion

Prove a uniform norm bound for the finite matrix with off-diagonal entries $\sqrt{\delta_r\delta_s}/(\lambda_r-\lambda_s)$ and zero diagonal. Multiplication by $i$ makes this real skew-symmetric matrix Hermitian. A bound on its diagonal quadratic form gives the operator norm bound and hence the bilinear inequality after rescaling the two vectors. The application requires an absolute constant, not the paper's particular constant.

## Sources

- Hugh L. Montgomery and Robert C. Vaughan, *Hilbert’s inequality*, Journal of the London Mathematical Society, 1974, Theorem 2 (diagonal form).
- Levent Alpöge and Ralph Furman, [More than two thirds of the zeta zeros are simple and on the critical line](https://arxiv.org/abs/2608.13637), Lemma 2.2 (bilinear form).
- Anthropic, [weighted bilinear interface](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/Hypotheses.lean#L98-L111) and [formalized absolute-constant bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/MV/Final.lean#L10-L31).
