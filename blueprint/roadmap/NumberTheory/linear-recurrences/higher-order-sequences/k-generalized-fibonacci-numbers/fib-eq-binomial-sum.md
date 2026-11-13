# Fibonacci numbers as a truncated binomial sum

Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$), and for an integer $x$ and a natural number
$j$ let $\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For every natural number $n \ge 2$,

$$
F_n = 2^{n-2} \sum_{\ell=0}^{\lfloor (n-1)/3 \rfloor}
\left(\binom{3\ell - n}{\ell} - \binom{3\ell - n}{\ell - 1}\right) 2^{-3\ell},
$$

where the term $\binom{3\ell - n}{\ell - 1}$ is taken to be $0$ for $\ell = 0$.

## Sources

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Corollary 13 (`jis-2024-24.1.1-cor-13`).
