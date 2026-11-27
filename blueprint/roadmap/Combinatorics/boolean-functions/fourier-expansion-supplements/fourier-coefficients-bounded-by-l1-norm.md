# Fourier coefficients bounded by the L¹ norm and values by the spectral norm

For every real function $f$ on $\{-1,1\}^n$: $|\hat f(S)| \le \mathbb{E}|f|$ for every $S$, i.e. $\|\hat f\|_\infty \le \|f\|_1$; and $|f(x)| \le \sum_S |\hat f(S)|$ for every $x$, i.e. $\|f\|_\infty \le \|\hat f\|_1$. The first is the $p = 1$ endpoint of the Hausdorff–Young inequality $\|\hat f\|_{p'} \le \|f\|_p$ ($1 \le p \le 2$, uniform measure on the cube, counting measure on sets); the second is the same endpoint for Fourier inversion.

## Proof sketch

$\hat f(S) = \mathbb{E}[f \chi_S]$ with $|\chi_S| = 1$; and $f(x) = \sum_S \hat f(S)\chi_S(x)$ by Fourier inversion.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [Fourier inversion on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/sum-bool-fourier-coeff-mul-cube-chi.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
