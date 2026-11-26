# Boolean functions of degree at most k have Fourier coefficients in 2^{1−k}ℤ

If $f : \{-1,1\}^n \to \mathbb{Z}$ has Fourier degree at most $k$, then every $\hat f(S)$ lies in $2^{-k}\mathbb{Z}$. If $f : \{-1,1\}^n \to \{-1,1\}$ has degree at most $k \ge 1$, then every $\hat f(S)$ lies in $2^{1-k}\mathbb{Z}$ (and in $\mathbb{Z}$ for $k = 0$). Consequently such an $f$ has at most $4^{k-1}$ nonzero coefficients and depends on at most $k\,2^{k-1}$ coordinates.

## Proof sketch

Write $f$ in the $\{0,1\}$-monomial basis via Möbius inversion: integer values and degree at most $k$ give integer coefficients on monomials $\prod_{i\in T} \frac{1 - x_i}{2}$ with $|T| \le k$, whose $\chi$-expansions have denominators $2^{|T|}$. For $\pm1$-valued $f$ apply this to the integer-valued $(1 - f)/2$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Zeta and Möbius transforms on the subset lattice](../../../ComputerScience/algebraic-and-numerical-algorithms/fast-zeta-transform-and-subset-convolution/zeta-and-mobius-transforms.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
