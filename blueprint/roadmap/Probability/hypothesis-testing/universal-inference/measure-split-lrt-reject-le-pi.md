# Split likelihood ratio test for an i.i.d. sample

In the setting of the [i.i.d. universal confidence set](measure-not-mem-universal-confidence-set-2.md),
let $\Theta_0$ contain the true parameter $\theta^*$ and let $\hat\theta_0$ be a maximiser of the split
likelihood $\mathcal L_0$ over $\Theta_0$ (only $\mathcal L_0(\theta) \le \mathcal L_0(\hat\theta_0)$ for
$\theta \in \Theta_0$ is used). The split likelihood ratio test rejects
$H_0 : \theta^* \in \Theta_0$ when $U_n = \mathcal L_0(\hat\theta_1) / \mathcal L_0(\hat\theta_0) > 1/\alpha$. For every
$0 < \alpha < \infty$,

$$\bigl(\rho \otimes (p_{\theta^*}\nu)^{\otimes m}\bigr)\bigl(\{(w, y) : \alpha^{-1} \mathcal L_0(\hat\theta_0(y)) < \mathcal L_0(\hat\theta_1(w))\}\bigr) \le \alpha.$$

When $p_{\theta^*}$ is a probability density this is the type I error bound $P_{\theta^*}(U_n > 1/\alpha) \le \alpha$; when
every $p_\theta$, $\theta \in \Theta_0$, is a probability density, it gives
$\sup_{\theta^* \in \Theta_0} P_{\theta^*}(U_n > 1/\alpha) \le \alpha$.

The test applies to irregular models, such as testing the number of components of a Gaussian
mixture, where the ordinary likelihood ratio statistic has no tractable limit. When both halves
are independent samples from the true model (possibly of different sizes), the crossfit version,
which averages $U_n$ with the statistic obtained by swapping the two halves, satisfies the same
bound by the same argument; with an arbitrary law $\rho$ for the first half, as above, it need not. The ratio is written without division: $U_n > 1/\alpha$ is
$\alpha^{-1} \mathcal L_0(\hat\theta_0) < \mathcal L_0(\hat\theta_1)$ in $[0, \infty]$. This fixes the
convention $0/0 = 0$ (no rejection when both likelihoods vanish), which matters for the type I
error only on samples of probability zero under the true parameter.

## Informally uses

- [Type I error of the split likelihood ratio test](measure-split-lrt-reject-le.md): the general statement, applied to the joint density $\prod_i p_\theta(y_i)$.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, arXiv:1912.11436v4 (21 October 2022); published in Proc. Natl. Acad. Sci. USA 117 (2020) 16880–16890. Theorem, remark and equation numbers refer to the arXiv version, which is the one read. Theorem 3, equation (9).
