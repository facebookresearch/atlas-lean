# The Margulis–Russo formula

Let $0 < p < 1$, let the bits $x_1,\dots,x_n \in \{0,1\}$ be independent with $\Pr[x_i = 1] = p$, and let $\mu = 1 - 2p$ and $\sigma = 2\sqrt{p(1-p)}$ be the mean and standard deviation of each sign $(-1)^{x_i}$. For every real $h$ on $\{0,1\}^n$, with $\hat h^{(p)}$ its Fourier coefficients in the $p$-biased basis $\phi_i(x) = ((-1)^{x_i} - \mu)/\sigma$ and $\mathbb{E}_p[h]$ viewed as a function of $\mu$,

$$\frac{d}{d\mu}\mathbb{E}_{p}[h] = \frac{1}{\sigma}\sum_{i=1}^n \hat h^{(p)}(\{i\}).$$

For a monotone Boolean $f$ this is [Russo's formula](../../../Probability/correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/has-deriv-at-prob-eq-sum-pivotal-prob.md) for the derivative in $p$ of the probability of an increasing event, rewritten in the $p$-biased Fourier basis.

## Proof sketch

Differentiate the product weights coordinate by coordinate: $\frac{\partial}{\partial p}\mathbb{E}_p[h] = \sum_i \mathbb{E}_p[h(x^{i \to 1}) - h(x^{i \to 0})]$, and for monotone Boolean $f$ the difference is the indicator that $i$ is pivotal.

## Depends on

- [Expectation under the p-biased product measure](expectation-under-the-p-biased-measure.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- M. Talagrand, "On Russo's Approximate Zero-One Law", Annals of Probability 22(3), 1994.
