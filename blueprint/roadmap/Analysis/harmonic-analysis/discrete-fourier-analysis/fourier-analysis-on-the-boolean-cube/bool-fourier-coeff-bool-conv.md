# Convolution theorem on the Boolean cube

For all $f, g : \{-1, 1\}^n \to \mathbb{R}$ and every $S \subseteq \{0, \dots, n-1\}$,

$$\widehat{f * g}(S) = \hat f(S)\, \hat g(S).$$

The proof substitutes $x = z y$ in $\mathbb{E}_x \mathbb{E}_y[f(y) g(x y) \chi_S(x)]$ and uses
$\chi_S(z y) = \chi_S(z)\chi_S(y)$.
The same statement for the discrete Fourier transform on a cyclic group is the
[convolution theorem for the discrete Fourier transform](../inv-dft-mul-dft.md).

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Theorem 1.27.
