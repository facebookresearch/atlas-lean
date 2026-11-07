# Difference binomial series at the $k$-Fibonacci root

Let $k \ge 2$ be a natural number
and $\rho > 0$ a real number with $\rho^k = 1 + \rho + \cdots + \rho^{k-1}$, and for an integer
$x$ and a natural number $j$ let $\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For every natural number
$n \ne 1$ the series below converges absolutely and

$$
2^{n-2} \sum_{\ell \ge 0} \left(\binom{(k+1)\ell - n}{\ell} - \binom{(k+1)\ell - n}{\ell - 1}\right)
2^{-(k+1)\ell} = \frac{\rho - 1}{(k+1)\rho - 2k} \rho^{n-1},
$$

where the term $\binom{(k+1)\ell - n}{\ell - 1}$ is taken to be $0$ for $\ell = 0$.

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 8 (`jis-2024-24.1.1-thm-8`), with `As_n^{(k)}` from equation (8).
