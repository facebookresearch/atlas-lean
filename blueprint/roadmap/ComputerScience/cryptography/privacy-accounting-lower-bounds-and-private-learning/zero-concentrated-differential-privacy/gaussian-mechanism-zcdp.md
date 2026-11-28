# The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance

Let $q$ have $\ell_2$-sensitivity $\Delta$ and $M(S) = q(S) + \mathcal{N}(0, \sigma^2 I)$. Then $M$ is $\dfrac{\Delta^2}{2\sigma^2}$-zCDP, with equality of Rényi divergences for a neighbouring pair attaining the sensitivity: $D_\alpha\big(\mathcal{N}(a, \sigma^2 I) \| \mathcal{N}(b, \sigma^2 I)\big) = \dfrac{\alpha\|a - b\|_2^2}{2\sigma^2}$ for every $\alpha > 1$.

## Proof sketch

Compute $\int \big(\frac{dP}{dQ}\big)^{\alpha}dQ$ for two Gaussians with equal covariance by completing the square in the exponent: the integral equals $\exp\big(\alpha(\alpha-1)\|a - b\|^2/(2\sigma^2)\big)$, and dividing the logarithm by $\alpha - 1$ gives the formula. Maximizing over neighbours gives the zCDP parameter.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Proposition 1.6 and Lemma 2.5.
- I. Mironov, "Renyi Differential Privacy", IEEE CSF (2017), arXiv:1702.07476.
