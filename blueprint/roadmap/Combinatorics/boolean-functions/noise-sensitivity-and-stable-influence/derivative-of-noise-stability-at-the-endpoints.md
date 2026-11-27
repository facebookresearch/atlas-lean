# The derivative of noise stability at 0 and at 1

For every real $f$ on $\{-1,1\}^n$, the function $\rho \mapsto \mathrm{Stab}_\rho[f]$ has derivative $\mathbf{W}^1[f]$ at $\rho = 0$ and $\mathbf{I}[f]$ at $\rho = 1$. For Boolean $f$ this gives $\frac{d}{d\delta}\mathrm{NS}_\delta[f]\big|_{\delta = 0} = \mathbf{I}[f]$.

## Proof sketch

This is the case $\rho \in \{0, 1\}$ of $\frac{d}{d\rho}\mathrm{Stab}_\rho[f] = \sum_{k \ge 1} k\rho^{k-1}\mathbf{W}^k[f]$ (the constant level contributes nothing; $0^0 = 1$): at $\rho = 0$ only $k = 1$ survives, giving $\mathbf{W}^1[f]$, and at $\rho = 1$ the derivative is $\sum_k k\mathbf{W}^k[f] = \mathbf{I}[f]$. Since $\mathrm{NS}_\delta[f] = \frac12 - \frac12\mathrm{Stab}_{1-2\delta}[f]$, the chain rule gives $\frac{d}{d\delta}\mathrm{NS}_\delta[f] = \frac{d}{d\rho}\mathrm{Stab}_\rho[f]\big|_{\rho = 1-2\delta}$.

## Depends on

- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Noise sensitivity](noise-sensitivity.md)

## Proof depends on

- [Total stable influence is the derivative of noise stability](total-stable-influence-is-derivative-of-noise-stability.md)
- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)
- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
