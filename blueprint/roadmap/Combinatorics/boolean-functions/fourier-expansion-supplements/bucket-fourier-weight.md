# Fourier weight on the sets with a given trace on a coordinate set

For a real function $F$ on $\{-1,1\}^n$, a set $J \subseteq [n]$ and $S \subseteq J$, the *bucket weight* is

$$\mathbf{W}^{S \mid \bar J}[F] = \sum_{T \subseteq [n] \setminus J} \hat F(S \cup T)^2,$$

the Fourier weight on the sets whose trace on $J$ is $S$. For fixed $J$ the buckets partition all sets, and $\mathbf{W}^{S\mid\bar J}[F] = \mathbb{E}_{z}\big[\widehat{F_{\bar J \to z}}(S)^2\big]$, the expected squared coefficient of $S$ in the restriction of $F$ fixing the coordinates outside $J$ to a uniform $z$. This underlies the Goldreich–Levin and Kushilevitz–Mansour algorithms for finding heavy Fourier coefficients.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- O. Goldreich and L. A. Levin, "A Hard-Core Predicate for All One-Way Functions", STOC 1989.
- E. Kushilevitz and Y. Mansour, "Learning Decision Trees Using the Fourier Spectrum", SIAM Journal on Computing 22(6), 1993.
