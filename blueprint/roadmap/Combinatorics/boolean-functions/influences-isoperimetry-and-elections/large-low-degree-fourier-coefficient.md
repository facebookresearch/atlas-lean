# A Boolean function of variance at least 1/2 has a large low-degree Fourier coefficient

Let $f : \{-1,1\}^n \to \{-1,1\}$ have $\mathrm{Var}[f] \ge 1/2$ and $\mathbf{I}[f] \le K$. Then some nonempty $S$ with $|S| \le 8K$ satisfies $\hat f(S)^2 \ge \exp(-O(K^2))$; explicitly $\hat f(S)^2 \ge \frac{1}{4(M + 1)^{\lfloor 8K \rfloor}}$ with $M = \frac{256}{9}K^3 81^{8K}$.

## Proof sketch

By Markov at least $1/4$ of the Fourier weight lies on nonempty sets of size at most $8K$; Friedgut's argument shows these sets lie within a junta of at most $M$ coordinates up to small weight, and there are at most $(M + 1)^{8K}$ such sets, so one carries the stated weight.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [Friedgut's Junta Theorem](../structure-theorems-for-boolean-functions/friedgut-junta-theorem.md)
- [Low total influence implies low-degree spectral concentration](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/sum-sq-card-gt-le-of-pos.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- E. Friedgut, "Boolean Functions With Low Average Sensitivity Depend On Few Coordinates", Combinatorica 18(1), 1998.
