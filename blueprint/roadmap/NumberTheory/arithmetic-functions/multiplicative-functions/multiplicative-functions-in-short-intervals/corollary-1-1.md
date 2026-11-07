# Liouville's function does not correlate with polynomial phases on short intervals on average

Let $\lambda$ be the Liouville function, extended to the integers by $\lambda(n) = 0$ for
$n \le 0$, let $k$ be a natural number and let $\theta$ be a real number with $0 < \theta < 1$.
For real $x$ and $H > 0$ write

$$
\|\lambda\|_{u^{k+1}[x, x+H]} = \sup_{\deg P \le k} \frac{1}{H}
\Bigl| \sum_{\lceil x \rceil \le n \le \lfloor x + H \rfloor} \lambda(n) e^{-2\pi i P(n)} \Bigr|,
$$

the supremum taken over real polynomials $P$ of degree at most $k$. Then

$$
\int_X^{2X} \|\lambda\|_{u^{k+1}[x, x + X^\theta]} \, dx = o(X)
$$

as the real number $X$ tends to infinity.

## Sources

- K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, and T. Ziegler, `Higher uniformity of bounded multiplicative functions in short intervals on average`, Annals of Math, 197 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-2-BoundedMultiplicativeFunctions.lean Via leanprover/lean-eval@38361be, problem `annals_bounded_multiplicative_functions`.
