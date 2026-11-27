# Fourier coefficients of the coordinate Laplacian

For $f : \{-1, 1\}^n \to \mathbb{R}$ and a coordinate $i$, the coordinate Laplacian
$L_i f(x) = (f(x) - f(x^{\oplus i}))/2$ has Fourier expansion

$$L_i f = \sum_{S \ni i} \hat f(S)\, \chi_S :$$

$\widehat{L_i f}(S) = \hat f(S)$ if $i \in S$ and $0$ otherwise. In particular
$\mathrm{Inf}_i[f] = \mathbb{E}[(L_i f)^2] = \sum_{S \ni i} \hat f(S)^2$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Definition 2.25 and Proposition 2.26.
