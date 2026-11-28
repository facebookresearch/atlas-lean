# Primal–dual conversion between f-DP and families of approximate DP guarantees

Let $f$ be a symmetric trade-off function and $f^*(y) = \sup_{\alpha \in [0,1]} \big(y\alpha - f(\alpha)\big)$ its convex conjugate. Then a mechanism is $f$-DP if and only if it is $(\varepsilon, \delta(\varepsilon))$-DP for every $\varepsilon \ge 0$, where

$$
\delta(\varepsilon) = 1 + f^*(-e^{\varepsilon}).
$$

In particular, for $\mu > 0$, a mechanism is $\mu$-GDP if and only if it is $(\varepsilon, \delta(\varepsilon))$-DP for all $\varepsilon \ge 0$ with

$$
\delta(\varepsilon) = \Phi\Big(-\frac{\varepsilon}{\mu} + \frac{\mu}{2}\Big) - e^{\varepsilon}\, \Phi\Big(-\frac{\varepsilon}{\mu} - \frac{\mu}{2}\Big).
$$

The formula divides by $\mu$ and is undefined at $\mu = 0$ (it reads $0/0$ at $\varepsilon = 0$). The case $\mu = 0$ is perfect privacy, $G_0(\alpha) = 1 - \alpha$, and then $\delta(\varepsilon) = 1 + G_0^*(-e^{\varepsilon}) = 0$ for every $\varepsilon \ge 0$: a mechanism is $0$-GDP if and only if it is $(\varepsilon, 0)$-DP for all $\varepsilon \ge 0$, that is, $(0,0)$-DP.

## Proof sketch

A convex nonincreasing function is the pointwise supremum of its supporting lines; the supporting line of slope $-e^{\varepsilon}$ to $f$ is exactly the line $1 - \delta - e^{\varepsilon}\alpha$ with $\delta = 1 + f^*(-e^{\varepsilon})$, and by symmetry of $f$ the same $\delta$ handles the line of slope $-e^{-\varepsilon}$. Hence $T \ge f$ if and only if $T \ge f_{\varepsilon, \delta(\varepsilon)}$ for all $\varepsilon$, which by the previous lemma is $(\varepsilon,\delta(\varepsilon))$-DP. For $G_\mu$ the conjugate is computed from the Gaussian likelihood ratio test at threshold $e^{\varepsilon}$.

## Depends on

- [Gaussian differential privacy](gaussian-differential-privacy.md)

## Proof depends on

- [Approximate differential privacy as f-differential privacy](epsilon-delta-dp-as-f-dp.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383v3, Proposition 2.12 and Corollary 2.13.
