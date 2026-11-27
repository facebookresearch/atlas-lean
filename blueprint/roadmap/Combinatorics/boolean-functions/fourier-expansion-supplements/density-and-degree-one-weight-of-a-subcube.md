# Density and degree-one weight of a subcube

Let $K \subseteq [n]$ with $|K| = k$ and $b \in \{-1,1\}^K$, and let $f = \mathbf{1}_C$ be the $0/1$ indicator of the subcube $C = \{x : x_i = b_i \ \forall i \in K\}$ of codimension $k$. Then $\mathbb{E}[f] = 2^{-k}$, $\hat f(S) = 2^{-k}\prod_{i \in S} b_i$ for $S \subseteq K$ and $0$ otherwise, and

$$\mathbf{W}^1[f] = k\, 2^{-2k}.$$

So subcubes attain the Level-1 inequality up to a constant factor: $\mathbf{W}^1[f] = \alpha^2\log_2(1/\alpha)$ with $\alpha = 2^{-k}$.

## Proof sketch

$f = \prod_{i \in K}\frac{1 + b_i x_i}{2}$; expanding the product gives the coefficients, and there are $k$ singletons, each of squared coefficient $4^{-k}$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Fourier weight at each degree](fourier-weight-at-each-degree.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
