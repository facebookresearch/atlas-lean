# Noise operator is diagonal in the Walsh basis

Let $E$ be a finite set and $\rho$ a real number. For every $f : \{0, 1\}^E \to \mathbb{R}$,

$$T_\rho f = \sum_{S \subseteq E} \rho^{\lvert S\rvert}\, \hat f(S)\, \chi_S,$$

where $T_\rho f(x) = \sum_y \prod_{i \in E} \kappa_i(x, y)\, f(y)$ with $\kappa_i = (1 + \rho)/2$ if $x_i = y_i$ and $(1 - \rho)/2$ otherwise, $\hat f(S)$ are the [Walsh–Fourier coefficients](khc-fourier-coeff.md) and $\chi_S(x) = \prod_{i \in S} (-1)^{x_i}$.
