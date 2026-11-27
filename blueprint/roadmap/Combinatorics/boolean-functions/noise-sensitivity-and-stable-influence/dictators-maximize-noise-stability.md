# Dictators maximize the noise stability of unbiased Boolean functions

If $f : \{-1,1\}^n \to \{-1,1\}$ has $\mathbb{E}[f] = 0$, then $\mathrm{Stab}_\rho[f] \le \rho$ for $0 \le \rho \le 1$; for $0 < \rho < 1$ equality holds iff $f = \pm \chi_{\{i\}}$ for some $i$ (a dictator or anti-dictator).

## Proof sketch

With $\hat f(\emptyset) = 0$, $\mathrm{Stab}_\rho[f] = \sum_{k \ge 1}\rho^k\mathbf{W}^k[f] \le \rho\sum_{k\ge1}\mathbf{W}^k[f] = \rho$, with equality for $0 < \rho < 1$ iff all weight is at degree one, i.e. $\mathbf{W}^1[f] = 1$. Then $n \ge 1$ (a constant on zero bits is not unbiased), and the Friedgut–Kalai–Naor theorem at $\delta = 0$ makes $f$ a literal; conversely a literal has $\mathrm{Stab}_\rho = \rho$.

## Depends on

- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)
- [Friedgut–Kalai–Naor (FKN) Theorem](../structure-theorems-for-boolean-functions/fkn-theorem.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
