# $k$-Fibonacci numbers as truncated binomial sums

Let $k \ge 2$ and let
$(F_n)_{n \ge 0}$ be the $k$-Fibonacci sequence, given by $F_0 = \dots = F_{k-2} = 0$,
$F_{k-1} = 1$ and $F_{m+k} = F_m + F_{m+1} + \dots + F_{m+k-1}$ for all $m \ge 0$. For integers
$a$ and $j \ge 0$ write $\binom{a}{j} = a(a-1)\cdots(a-j+1)/j!$, and put $\binom{a}{-1} = 0$.
For $n \ge 2$ let $G_n^{(k)}$ be the truncated binomial sum
$G_n^{(k)} = 2^{n-2} \sum_{\ell=0}^{\lfloor (n-1)/(k+1) \rfloor} \left(\binom{(k+1)\ell-n}{\ell} -
\binom{(k+1)\ell-n}{\ell-1}\right) 2^{-(k+1)\ell}$. Then $F_{n+k-2} = G_n^{(k)}$ for every
$n \ge 2$.

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 9 (`jis-2024-24.1.1-thm-9`).
