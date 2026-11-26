# Low total influence or noise sensitivity gives low-degree spectral concentration

For every real $f$ on $\{-1,1\}^n$ and $t \ge 0$: $\mathbf{W}^{> t}[f] \le \mathbf{I}[f]/(t+1)$, and for Boolean $f$ and $0 < \delta \le 1/2$, $\mathbf{W}^{\ge 1/\delta}[f] \le 3\,\mathrm{NS}_\delta[f]$. Hence functions with small noise sensitivity, such as linear threshold functions, are $\varepsilon$-concentrated on degree $O(1/\varepsilon^2)$ and are learnable by the low-degree algorithm.

## Proof sketch

$\mathbf{I}[f] = \sum_S |S|\hat f(S)^2 \ge (t + 1)\mathbf{W}^{> t}[f]$. For the noise bound, $2\mathrm{NS}_\delta = \sum_S (1 - (1 - 2\delta)^{|S|})\hat f(S)^2$ and $1 - (1 - 2\delta)^{k} \ge 1 - e^{-2} \ge 2/3$ for $k \ge 1/\delta$.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Noise sensitivity](noise-sensitivity.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)

## Proof depends on

- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- N. Linial, Y. Mansour and N. Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM 40(3), 1993.
