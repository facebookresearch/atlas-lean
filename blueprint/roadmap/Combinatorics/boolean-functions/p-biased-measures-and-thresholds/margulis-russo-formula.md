# The Margulis–Russo formula

For every real $h$ on $\{0,1\}^n$ and $0 < p < 1$, viewing $\mathbb{E}_p[h]$ as a function of the mean $\mu = 1 - 2p$ of the $\pm1$ bits,

$$\frac{d}{d\mu}\mathbb{E}_{p}[h] = \frac{1}{\sigma}\sum_{i=1}^n \hat h^{(p)}(\{i\}).$$

For monotone Boolean $f$ (with values in $\{0,1\}$, increasing in each bit), as polynomials in $p$,

$$\frac{d}{dp}\Pr_p[f = 1] = \sum_{i=1}^n \Pr_p[x_i \text{ is pivotal for } f],$$

the expected number of pivotal coordinates (Russo's formula).

## Proof sketch

Differentiate the product weights coordinate by coordinate: $\frac{\partial}{\partial p}\mathbb{E}_p[h] = \sum_i \mathbb{E}_p[h(x^{i \to 1}) - h(x^{i \to 0})]$, and for monotone Boolean $f$ the difference is the indicator that $i$ is pivotal.

## Depends on

- [Expectation under the p-biased product measure](expectation-under-the-p-biased-measure.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- M. Talagrand, "On Russo's Approximate Zero-One Law", Annals of Probability 22(3), 1994.
