# Alternating binomial formula for the $k$-Fibonacci numbers

Let $k \ge 2$ be a natural
number and let $F_n^{(k)}$ be the $k$-Fibonacci numbers: $F_i^{(k)} = 0$ for $i < k - 1$,
$F_{k-1}^{(k)} = 1$ and $F_{m+k}^{(k)} = F_m^{(k)} + F_{m+1}^{(k)} + \cdots + F_{m+k-1}^{(k)}$ for
every $m \ge 0$. For an integer $x$ and a natural number $j$ let
$\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. Then for every natural number $n \ge k$,

$$
F_n^{(k)} = 2^{n-k} + \sum_{\ell=1}^{\lfloor (n-k+1)/(k+1) \rfloor} (-1)^\ell
\left(\binom{n - (\ell+1)k + 2}{\ell} - \binom{n - (\ell+1)k}{\ell - 2}\right)
2^{n - (k+1)\ell - k},
$$

where the term $\binom{n - (\ell+1)k}{\ell - 2}$ is taken to be $0$ for $\ell = 1$.

The paper assumes $n \ne 2k - 1$; for $n = 2k - 1$ the sum is empty and both sides equal
$2^{k-1}$.

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Corollary 14 (`jis-2024-24.1.1-cor-14`).
