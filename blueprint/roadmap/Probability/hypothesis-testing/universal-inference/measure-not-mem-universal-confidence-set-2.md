# Universal confidence set for an i.i.d. sample

Let $\Theta$, $\mathcal{Y}$ and $\mathcal{W}$ be measurable spaces, $\nu$ a σ-finite measure on $\mathcal{Y}$, and
$p_\theta : \mathcal{Y} \to [0, \infty]$ functions jointly measurable in $(\theta, y)$ with $\int p_\theta \, d\nu \le 1$
(probability densities or sub-densities). Let $m \in \mathbb{N}$ ($m = 0$ is allowed), $\rho$ a probability measure
on $\mathcal{W}$, $\hat\theta_1 : \mathcal{W} \to \Theta$ a measurable estimator and $\theta^* \in \Theta$. With the
split likelihood $\mathcal L_0(\theta) = \prod_{i=1}^m p_\theta(y_i)$ of $y = (y_1, \dots, y_m)$ and the universal set
$C(w, y) = \{\theta : \mathcal L_0(\hat\theta_1(w)) \le \alpha^{-1} \mathcal L_0(\theta)\}$, for every $0 < \alpha < \infty$

$$\bigl(\rho \otimes (p_{\theta^*}\nu)^{\otimes m}\bigr)\bigl(\{(w, y) : \theta^* \notin C(w, y)\}\bigr) \le \alpha.$$

When $p_{\theta^*}$ is a probability density, this says that the universal set misses $\theta^*$ with probability at
most $\alpha$ when $D_0 = (Y_1, \dots, Y_m)$ is i.i.d. with density $p_{\theta^*}$, independent of $D_1 \sim \rho$.

The source splits $2n$ observations into halves of size $n$ and remarks that equal sizes are not
necessary; in the statement above $D_1$ is arbitrary and $D_0$ has size $m$. Ratios are written without division: $T(\theta) \le 1/\alpha$ is
$\mathcal L_0(\hat\theta_1) \le \alpha^{-1} \mathcal L_0(\theta)$ in $[0, \infty]$. This fixes the
convention $0/0 = 0$, which matters only on samples of probability zero under the true parameter.

## Informally uses

- [Finite-sample validity of the universal confidence set](measure-not-mem-universal-confidence-set.md): the general statement, applied to the joint density $\prod_i p_\theta(y_i)$ with respect to $\nu^{\otimes m}$; the joint density integrates to $\prod_i \int p_\theta \, d\nu \le 1$.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, arXiv:1912.11436v4 (21 October 2022); published in Proc. Natl. Acad. Sci. USA 117 (2020) 16880–16890. Theorem, remark and equation numbers refer to the arXiv version, which is the one read. Theorem 1.
