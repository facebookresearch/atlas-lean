# A Boolean function of variance at least 1/2 has a large low-degree Fourier coefficient

Let $f : \{-1,1\}^n \to \{-1,1\}$ have $\mathrm{Var}[f] \ge 1/2$ and $\mathbf{I}[f] \le K$. Then some nonempty $S$ with $|S| \le 8K$ satisfies $\hat f(S)^2 \ge \exp(-O(K^2))$; explicitly $\hat f(S)^2 \ge \frac{1}{4(M + 1)^{\lfloor 8K \rfloor}}$ with $M = 64K^3\, 9^{\lfloor 8K \rfloor}$. (Here $K \ge \mathbf{I}[f] \ge \mathrm{Var}[f] \ge 1/2$.)

## Proof sketch

Put $k = \lfloor 8K \rfloor$ and $\varepsilon = 1/8$. By Markov the weight on $|S| > k$ is at most $\mathbf{I}[f]/(k + 1) < 1/8$. For $J = \{j : \mathbf{Inf}_j[f] \ge \varepsilon^2/(\mathbf{I}[f]^2 9^k)\}$, the spectral part of Friedgut's argument bounds the weight on sets of size at most $k$ not contained in $J$ by $1/8$, and $|J| \le \mathbf{I}[f]^3 9^k/\varepsilon^2 \le M$. Since $\hat f(\emptyset)^2 = 1 - \mathrm{Var}[f] \le 1/2$, the nonempty subsets of $J$ of size at most $k$ carry weight at least $1 - \frac12 - \frac18 - \frac18 = \frac14$; there are at most $(M + 1)^k$ of them, so one carries weight at least $1/(4(M + 1)^k)$ (O'Donnell, Cor. 9.32).

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)

## Proof depends on

- [Spectral part of Friedgut's argument](../structure-theorems-for-boolean-functions/sum-sq-not-subset-le-of-influence.md)
- [Few coordinates have large influence](../structure-theorems-for-boolean-functions/card-influential-le.md)
- [Low total influence implies low-degree spectral concentration](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/sum-sq-card-gt-le-of-pos.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- E. Friedgut, "Boolean Functions With Low Average Sensitivity Depend On Few Coordinates", Combinatorica 18(1), 1998.
