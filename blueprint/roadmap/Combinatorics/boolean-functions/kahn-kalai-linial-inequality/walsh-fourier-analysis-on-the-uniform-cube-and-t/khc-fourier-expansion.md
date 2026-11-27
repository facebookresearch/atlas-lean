# Fourier inversion on the Boolean cube

For a finite set $E$, every $f : \{0, 1\}^E \to \mathbb{R}$ and every $x \in \{0, 1\}^E$,

$$f(x) = \sum_{S \subseteq E} \hat f(S)\, \chi_S(x),$$

where $\hat f(S)$ are the [Walsh–Fourier coefficients](khc-fourier-coeff.md) and $\chi_S(x) = \prod_{i \in S} (-1)^{x_i}$.
