# Fourier expansion of the noise operator

For every real number $\rho$, every function $f$
from the Boolean cube $\{-1, 1\}^n$ to $\mathbb{R}$ and every point $x$ of the cube,

$$T_\rho f(x) = \sum_{S \subseteq \{0, \dots, n-1\}} \rho^{|S|} \, \hat f(S) \, \chi_S(x),$$

where $T_\rho$ is the noise operator, $\hat f(S)$ is the Fourier coefficient of $f$ at $S$,
$\chi_S$ is the Fourier character of $S$, and $\rho^0 = 1$ also when $\rho = 0$.
