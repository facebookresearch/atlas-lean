# Fourier expansion of the coordinate derivative

For $f : \{-1, 1\}^n \to \mathbb{R}$ and a coordinate $i$, the derivative
$D_i f(x) = \big(f(x^{(i \mapsto 1)}) - f(x^{(i \mapsto -1)})\big)/2 = x_i\,(f(x) - f(x^{\oplus i}))/2$
has Fourier expansion

$$D_i f = \sum_{S \ni i} \hat f(S)\, \chi_{S \setminus \{i\}} :$$

$\widehat{D_i f}(S) = 0$ for $S \ni i$, and $\widehat{D_i f}(S) = \hat f(S \cup \{i\})$ for $S \not\ni i$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Definition 2.16 and Proposition 2.19.
