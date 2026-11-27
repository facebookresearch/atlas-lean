# The Hamming distance in the Fourier basis

For Boolean functions $f, g$ read as $F = (-1)^f$, $G = (-1)^g$, the relative Hamming distance is

$$\Pr_x[f(x) \ne g(x)] = \frac{1}{4}\mathbb{E}[(F - G)^2] = \frac14 \sum_S \big(\hat F(S) - \hat G(S)\big)^2.$$

The map $f \mapsto \hat F / 2$ is therefore an isometric embedding of Boolean functions with the square root of the relative Hamming distance into $\ell_2$; for $-1 \le \rho \le 1$ the related noise distance satisfies $\frac14\mathbb{E}_{(x,y)\ \rho\text{-correlated}}[(F(x) - F(y))^2] = \frac12(1 - \mathrm{Stab}_\rho[F])$.

## Proof sketch

Pointwise, $(F - G)^2$ is $0$ where $f = g$ and $4$ elsewhere; apply Parseval to $F - G$. For the noise distance, expand $\mathbb{E}[F(x)F(y)] = \mathrm{Stab}_\rho[F]$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
