# Fourier weight at each degree

For a real function $f$ on $\{-1,1\}^n$ with Fourier coefficients $\hat f(S)$, the *Fourier weight at degree $k$* is $\mathbf{W}^k[f] = \sum_{|S| = k} \hat f(S)^2$, and $\mathbf{W}^{\le k}[f] = \sum_{j \le k}\mathbf{W}^j[f]$, $\mathbf{W}^{> k}[f] = \sum_{j > k}\mathbf{W}^j[f]$. The *degree-$k$ part* is $f^{=k} = \sum_{|S| = k} \hat f(S)\chi_S$, and $f^{\le k} = \sum_{j \le k} f^{=j}$ is the *low-degree part*. By Parseval, $\sum_k \mathbf{W}^k[f] = \mathbb{E}[f^2]$, the parts $f^{=k}$ are pairwise orthogonal, and $\mathbb{E}[(f^{=k})^2] = \mathbf{W}^k[f]$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Fourier character on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/cube-chi.md)

## Proof depends on

- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)
- [Orthogonality of the Boolean cube characters](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/sum-cube-chi-mul-cube-chi-eq-ite.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
