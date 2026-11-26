# Many-fold composition of pure differential privacy converges to Gaussian differential privacy

For the trade-off function $f_{\varepsilon,0}(\alpha) = \max\{0,\, 1 - e^{\varepsilon}\alpha,\, e^{-\varepsilon}(1 - \alpha)\}$ of $(\varepsilon,0)$-differential privacy and the functionals $\mathrm{kl}(f) = -\int_0^1 \log|f'(x)|\,dx$, $\kappa_2(f) = \int_0^1 \log^2|f'(x)|\,dx$, $\kappa_3(f) = \int_0^1 \big|\log|f'(x)|\big|^3\,dx$,

$$
\mathrm{kl}(f_{\varepsilon,0}) = \varepsilon\,\frac{e^{\varepsilon} - 1}{e^{\varepsilon} + 1}, \qquad \kappa_2(f_{\varepsilon,0}) = \varepsilon^2, \qquad \kappa_3(f_{\varepsilon,0}) = \varepsilon^3 .
$$

Consequently, if $\varepsilon_n \to 0$ with $\sqrt{n}\,\varepsilon_n \to \mu$, then the $n$-fold composition of $(\varepsilon_n, 0)$-DP mechanisms satisfies $f_{\varepsilon_n,0}^{\otimes n} \to G_\mu$ uniformly: the $n$-fold composition of $(\mu/\sqrt n)$-DP mechanisms is asymptotically $\mu$-GDP.

## Proof sketch

$f_{\varepsilon,0}$ has slope $-e^{\varepsilon}$ on $[0, 1/(1+e^{\varepsilon})]$ and $-e^{-\varepsilon}$ on the rest, so $\log|f'| = \pm\varepsilon$ on intervals of lengths $1/(1+e^\varepsilon)$ and $e^\varepsilon/(1+e^\varepsilon)$, giving the three functionals by direct integration. Then $\sum\mathrm{kl} = n\varepsilon_n\tanh(\varepsilon_n/2) \to \mu^2/2$, $\sum\kappa_2 \to \mu^2$ and $\sum\kappa_3 = n\varepsilon_n^3 \to 0$, so the central limit theorem gives $G_{2K/s}$ with $2K/s = \mu^2/\mu = \mu$.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)
- [Gaussian differential privacy](gaussian-differential-privacy.md)
- [Tensor product of trade-off functions](tensor-product-of-trade-off-functions.md)

## Proof depends on

- [Central limit theorem for the composition of trade-off functions](f-dp-composition-central-limit-theorem.md)
- [Approximate differential privacy as f-differential privacy](epsilon-delta-dp-as-f-dp.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
