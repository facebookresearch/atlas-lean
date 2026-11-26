# Noise stability as a sum over Fourier levels

For every real $f$ on $\{-1,1\}^n$ and every real $\rho$, $\mathrm{Stab}_\rho[f] = \sum_{k=0}^n \rho^k\, \mathbf{W}^k[f]$. Consequently $\mathrm{Stab}_\rho[f]$ is a polynomial in $\rho$ with nonnegative coefficients summing to $\mathbb{E}[f^2]$, nondecreasing in $\rho \in [0,1]$.

## Proof sketch

Group the set form $\mathrm{Stab}_\rho[f] = \sum_S \rho^{|S|}\hat f(S)^2$ by $|S|$.

## Depends on

- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)
- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)

## Proof depends on

- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
