# KKL edge-isoperimetric theorem

For every nonconstant $f : \{-1,1\}^n \to \{-1,1\}$, writing $\tilde{\mathbf{I}} = \mathbf{I}[f]/\mathrm{Var}[f]$, some coordinate $i$ satisfies

$$\mathbf{Inf}_i[f] \ge \frac{9}{\tilde{\mathbf{I}}^2}\Big(\frac19\Big)^{\tilde{\mathbf{I}}}.$$

In particular, if $\mathbf{I}[f] \le K\,\mathrm{Var}[f]$ then some coordinate has influence at least $9^{-O(K)}$, and the maximum influence of a balanced function with total influence $O(1)$ is bounded below by a constant.

## Proof sketch

By the small-set expansion form of hypercontractivity applied to the derivatives, $\sum_i \mathbf{Inf}_i^{(1/3)}[f] \le \sum_i \mathbf{Inf}_i[f]^{3/2}$ (stable influences at $\rho = 1/3$). If every influence is below $\delta$, the right side is at most $\sqrt\delta\, \mathbf{I}[f]$. On the left, Fourier weight of degree at most $k$ contributes at least $3^{-k}$ times its size, and at least half the variance lies at degree at most $2\tilde{\mathbf{I}}$ by Markov; combining gives the bound.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [Stable influences are bounded by powers of influences](../noise-sensitivity-and-stable-influence/stable-influences-bounded-by-powers-of-influences.md)
- [Low total influence implies low-degree spectral concentration](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/sum-sq-card-gt-le-of-pos.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- J. Kahn, G. Kalai and N. Linial, "The Influence of Variables on Boolean Functions", FOCS 1988.
