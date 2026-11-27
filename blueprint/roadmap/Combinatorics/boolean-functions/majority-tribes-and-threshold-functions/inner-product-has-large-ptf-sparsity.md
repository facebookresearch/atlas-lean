# Inner product mod 2 has PTF sparsity at least 2^n

If a nonzero real function $p$ on $\{-1,1\}^{2n}$ with Fourier support contained in a family $\mathcal{T}$ satisfies $\mathrm{IP}_{2n}(z)\, p(z) \ge 0$ for all $z$, then $|\mathcal{T}| \ge 2^n$. In particular every PTF representation of the inner product modulo two has sparsity at least $2^n$.

## Proof sketch

$\mathbb{E}[\mathrm{IP}\cdot p] = \mathbb{E}|p| > 0$, while by flatness of the IP spectrum $\mathbb{E}[\mathrm{IP}\cdot p] = \sum_{S\in\mathcal{T}}\widehat{\mathrm{IP}}(S)\hat p(S) \le 2^{-n}\sum_S|\hat p(S)| \le 2^{-n}|\mathcal{T}|\max_S|\hat p(S)| \le 2^{-n}|\mathcal{T}|\,\mathbb{E}|p|$.

## Depends on

- [Polynomial threshold functions and sparsity](polynomial-threshold-functions.md)
- [Fourier spectrum of the inner product mod 2](../fourier-expansion-supplements/fourier-spectrum-of-inner-product-mod-2.md)

## Proof depends on

- [Fourier coefficients bounded by the L¹ norm and values by the spectral norm](../fourier-expansion-supplements/fourier-coefficients-bounded-by-l1-norm.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
