# Binomial-sum formula for the $k$-Fibonacci numbers

Let $k \ge 2$ and let
$(F_n)_{n \ge 0}$ be the $k$-Fibonacci sequence, given by $F_0 = \dots = F_{k-2} = 0$,
$F_{k-1} = 1$ and $F_{m+k} = F_m + F_{m+1} + \dots + F_{m+k-1}$ for all $m \ge 0$. For integers
$a$ and $j \ge 0$ write $\binom{a}{j} = a(a-1)\cdots(a-j+1)/j!$, and put $\binom{a}{-1} = 0$.
Then for every $n \ge k$,

$$F_n = 2^{n-k} \sum_{\ell=0}^{\lfloor (n-k+1)/(k+1) \rfloor} \left(\binom{(k+1)\ell+k-n-2}{\ell} -
\binom{(k+1)\ell+k-n-2}{\ell-1}\right) 2^{-(k+1)\ell}.$$

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Corollary 12 (`jis-2024-24.1.1-cor-12`).
