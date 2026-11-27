# Rounding to the sign

Let $f : \{-1, 1\}^n \to \{-1, 1\}$ and $g : \{-1, 1\}^n \to \mathbb{R}$, and let
$h = \mathrm{sgn}(g)$, with $\mathrm{sgn}(0) \in \{-1, 1\}$ chosen arbitrarily (precisely: $h$ is
$\pm 1$-valued with $h(x) g(x) \ge 0$). Then

$$\mathrm{dist}(f, h) \le \mathbb{E}\big[(f - g)^2\big] = \|f - g\|_2^2,$$

since $|f(x) - g(x)| \ge 1$ wherever $f(x) \ne \mathrm{sgn}(g(x))$. This is the rounding step of the
Low-Degree Algorithm: a good $L^2$ approximation by a polynomial gives a good Boolean hypothesis.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Proposition 3.31.
