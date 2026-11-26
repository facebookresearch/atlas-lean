# Dictators maximize the noise stability of unbiased Boolean functions

If $f : \{-1,1\}^n \to \{-1,1\}$ has $\mathbb{E}[f] = 0$, then $\mathrm{Stab}_\rho[f] \le \rho$ for $0 \le \rho \le 1$; for $0 < \rho < 1$ equality holds iff $f = \pm \chi_{\{i\}}$ for some $i$ (a dictator or anti-dictator).

## Proof sketch

With $\hat f(\emptyset) = 0$, $\mathrm{Stab}_\rho[f] = \sum_{k \ge 1}\rho^k\mathbf{W}^k[f] \le \rho\sum_{k\ge1}\mathbf{W}^k[f] = \rho$, with equality for $0 < \rho < 1$ iff all weight is at degree one, i.e. $f$ is a literal.

## Depends on

- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)
- [Boolean functions with all Fourier weight at degree one are the literals](../fourier-expansion-supplements/degree-one-weight-one-implies-literal.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
