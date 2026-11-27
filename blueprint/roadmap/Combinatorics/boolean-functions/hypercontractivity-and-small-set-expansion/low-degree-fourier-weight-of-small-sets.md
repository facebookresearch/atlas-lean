# Low-degree Fourier weight of small sets

For every $A \subseteq \{-1,1\}^n$ of volume $\alpha$ and every $k \ge 0$, $\mathbf{W}^{\le k}[\mathbf{1}_A] \le 3^k\alpha^{3/2}$. Moreover for $0 < \rho \le 1$, $\mathbf{W}^1[\mathbf{1}_A] \le (\alpha^{2/(1+\rho)} - \alpha^2)/\rho$.

## Proof sketch

$\rho^k\mathbf{W}^{\le k} \le \sum_j\rho^j\mathbf{W}^j = \mathrm{Stab}_\rho \le \alpha^{2/(1+\rho)}$; take $\rho = 1/3$. For degree one, $\rho\mathbf{W}^1 \le \mathrm{Stab}_\rho - \mathbf{W}^0 = \mathrm{Stab}_\rho - \alpha^2$.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Small-Set Expansion Theorem](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bool-noise-stab-le-rpow-of-indicator.md)
- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
