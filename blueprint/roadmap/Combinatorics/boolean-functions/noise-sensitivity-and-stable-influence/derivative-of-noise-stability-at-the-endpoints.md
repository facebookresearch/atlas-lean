# The derivative of noise stability at 0 and at 1

For every real $f$ on $\{-1,1\}^n$, the function $\rho \mapsto \mathrm{Stab}_\rho[f]$ has derivative $\mathbf{W}^1[f]$ at $\rho = 0$ and $\mathbf{I}[f]$ at $\rho = 1$. For Boolean $f$ this gives $\frac{d}{d\delta}\mathrm{NS}_\delta[f]\big|_{\delta = 0} = \mathbf{I}[f]$.

## Proof sketch

Differentiate $\sum_k \rho^k\mathbf{W}^k[f]$ termwise; at $\rho = 1$ the derivative is $\sum_k k\mathbf{W}^k[f] = \mathbf{I}[f]$.

## Depends on

- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)

## Proof depends on

- [Noise stability as a sum over Fourier levels](noise-stability-as-a-sum-over-levels.md)
- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
