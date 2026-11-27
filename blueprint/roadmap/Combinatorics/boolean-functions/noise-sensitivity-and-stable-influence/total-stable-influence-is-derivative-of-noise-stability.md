# Total stable influence is the derivative of noise stability

For every real $f$ on $\{-1,1\}^n$ and every $\rho \in [0, 1]$ (one-sided derivatives at the endpoints), $\frac{d}{d\rho}\mathrm{Stab}_\rho[f] = \mathbf{I}^{(\rho)}[f] = \sum_{S \ne \emptyset} |S|\rho^{|S|-1}\hat f(S)^2$, with $0^0 = 1$.

## Proof sketch

Differentiate the Fourier formula $\mathrm{Stab}_\rho[f] = \sum_S\rho^{|S|}\hat f(S)^2$ term by term; the constant term $\hat f(\emptyset)^2$ contributes nothing.

## Depends on

- [Stable influence and total stable influence](stable-influence.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
