# Truncated binomial sum $G_n^{(k)}$

For an integer $x$ and a natural number $j$ let
$\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For natural numbers $k$ and $n$, the rational number
$G_n^{(k)}$ is

$$
G_n^{(k)} = 2^{n-2} \sum_{\ell=0}^{m}
\left(\binom{(k+1)\ell - n}{\ell} - \binom{(k+1)\ell - n}{\ell - 1}\right) 2^{-(k+1)\ell},
$$

where $m = \lfloor (n-1)/(k+1) \rfloor$ for $n \ge 1$ and $m = 0$ for $n = 0$, and the term
$\binom{(k+1)\ell - n}{\ell - 1}$ is taken to be $0$ for $\ell = 0$.

The paper defines $G_n^{(k)}$ only for $n, k \ge 2$.

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition before Proposition 10.
