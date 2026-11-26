# Polynomial threshold functions and sparsity

A function $f : \{-1,1\}^n \to \{-1,1\}$ is a *polynomial threshold function* (PTF) of degree at most $k$ if $f = \mathrm{sgn}(p)$ for a real multilinear polynomial $p$ of degree at most $k$ that vanishes nowhere on the cube; for $k = 1$ these are the linear threshold functions. More generally $f$ is represented on a family $\mathcal{T}$ of sets if $p$ has Fourier support in $\mathcal{T}$; the least $|\mathcal{T}|$ is the *sparsity* of $f$ as a PTF. Threshold functions $\mathrm{Th}^n_j$ (including majority, AND, OR and the constants) and the literals $\pm x_i$ are linear threshold functions.

## Depends on

- [Linear threshold function](../majority-is-least-stable-conjecture/is-linear-threshold-function.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
