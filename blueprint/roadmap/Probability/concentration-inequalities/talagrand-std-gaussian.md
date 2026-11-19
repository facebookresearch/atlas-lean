# Talagrand's transport inequality for the Gaussian measure

Let $\gamma$ be the standard Gaussian measure on a finite-dimensional real inner product space $E$.
For every probability measure $\mu$ on $E$ with finite second moment,

$$W_2(\mu, \gamma)^2 \le 2 \, H_\gamma(\mu),$$

where $H_\gamma(\mu) = \int \log \frac{d\mu}{d\gamma} \, d\mu$ is the relative entropy (Kullback–Leibler
divergence), equal to $+\infty$ unless $\mu \ll \gamma$. In Villani's terms, $\gamma$ satisfies the
inequality $T_2(1)$ of Definition 22.1, $W_2(\mu, \gamma) \le \sqrt{2 H_\gamma(\mu)}$, with a constant
independent of the dimension.

Since $W_1 \le W_2$, it implies $T_1(1)$, which by Villani's Theorem 22.10 is equivalent to Gaussian
concentration of $\gamma$. Villani obtains the example from Theorem 22.14 ($CD(K, \infty)$ implies
$T_2(K)$), the standard Gaussian satisfying $CD(1, \infty)$.

## Background

- [Wasserstein distance of order $p$](../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein.md):
  the distance $W_2$ in the inequality.
- [Monotonicity of the Wasserstein distances in the exponent](../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-mono.md):
  $W_1 \le W_2$, so $T_2$ implies $T_1$ (Villani, Remark 22.2).
- [Otto–Villani theorem](transport-cost-inequalities/satisfies-talagrand-of-satisfies-log-sob.md):
  in the literature, combined with Gross' logarithmic Sobolev inequality for the Gaussian measure
  (constant $1$), it gives this inequality with the same constant $2$; Villani's own route goes
  through $CD(K, \infty)$ instead. Gross' inequality is usually stated for smooth positive
  densities and the Otto–Villani hypothesis concerns nonnegative Lipschitz ones, so combining them
  needs an approximation argument.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Definition 22.1, Remark 22.2 and Example 22.15; M. Talagrand, *Transportation cost for Gaussian and other product measures*, Geom. Funct. Anal. 6 (1996), 587–600.
