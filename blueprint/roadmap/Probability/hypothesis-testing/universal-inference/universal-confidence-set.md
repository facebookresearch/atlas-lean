# Universal confidence set

Let $q_\theta$ be the densities of the second half $D_0$ of the sample, let $\theta_1$ be an
estimate computed from the first half $D_1$, and let $y$ be the observed second half. The universal
set is

$$C = \bigl\{\theta : q_{\theta_1}(y) \le \alpha^{-1} q_\theta(y)\bigr\},$$

that is, $\{\theta : T(\theta) \le 1/\alpha\}$ with the split likelihood ratio statistic
$T(\theta) = \mathcal L_0(\hat\theta_1)/\mathcal L_0(\theta)$ of equation (3). Ratios are written without division: $T(\theta) \le 1/\alpha$ is
$\mathcal L_0(\hat\theta_1) \le \alpha^{-1} \mathcal L_0(\theta)$ in $[0, \infty]$. This fixes the
convention $0/0 = 0$. The convention does not affect the coverage and type I error statements:
for them it matters only on samples of probability zero under the true parameter. It does decide
which other parameters belong to the set. When $\mathcal L_0(\hat\theta_1) = 0$, every $\theta$ with
$\mathcal L_0(\theta) = 0$ is in the set, and this can happen with positive probability.

## Related topics

- [Universal confidence set with real densities](universal-confidence-set-2.md): the form with real-valued densities and the level as a multiplier.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, arXiv:1912.11436v4 (21 October 2022); published in Proc. Natl. Acad. Sci. USA 117 (2020) 16880–16890. Theorem, remark and equation numbers refer to the arXiv version, which is the one read. Equations (3) and (4).
