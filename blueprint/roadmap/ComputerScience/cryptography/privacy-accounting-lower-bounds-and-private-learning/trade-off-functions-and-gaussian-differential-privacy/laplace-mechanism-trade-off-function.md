# Trade-off function of the Laplace mechanism

Let $\mathrm{Lap}(m, b)$ denote the Laplace distribution with location $m$ and scale $b$, and let $\mu = \Delta/b$ for $\Delta \ge 0$. Then for $\alpha \in [0,1]$,

$$
T\big(\mathrm{Lap}(0, b), \mathrm{Lap}(\Delta, b)\big)(\alpha) = \begin{cases} 1 - e^{\mu}\alpha, & \alpha < e^{-\mu}/2, \\ e^{-\mu}/(4\alpha), & e^{-\mu}/2 \le \alpha \le 1/2, \\ e^{-\mu}(1 - \alpha), & \alpha > 1/2. \end{cases}
$$

Hence the Laplace mechanism with $\ell_1$-sensitivity $\Delta$ and scale $b$ is $f$-DP for this function, which lies strictly above $f_{\mu,0}$ in the middle range: it is $(\Delta/b)$-DP, but $f$-DP describes it exactly.

## Proof sketch

The likelihood ratio of $\mathrm{Lap}(\Delta,b)$ to $\mathrm{Lap}(0,b)$ is monotone in $x$, so Neyman–Pearson tests reject for large $x$. A threshold $t$ has $\alpha(t) = \Pr_{\mathrm{Lap}(0,b)}[x > t]$ and $\beta(t) = \Pr_{\mathrm{Lap}(\Delta,b)}[x \le t]$; computing both from the Laplace distribution function on the three ranges $t < 0$, $0 \le t \le \Delta$, $t > \Delta$ and eliminating $t$ gives the three pieces.

## Depends on

- [f-differential privacy](f-differential-privacy.md)
- [Laplace mechanism](../../laplace-and-exponential-mechanisms/laplace-mechanism.md)

## Proof depends on

- [The Laplace mechanism is differentially private](../../laplace-and-exponential-mechanisms/laplace-mechanism-differentially-private.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
