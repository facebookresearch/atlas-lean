# Fibonacci closed form of a binomial sum with powers of two

Let $F_m$ denote the
Fibonacci numbers, with $F_0 = 0$ and $F_1 = 1$. For every natural number $n \ge 4$,

$$\sum_{k=1}^{\lfloor n/3 \rfloor - 1} \left( \binom{n-k-4}{2k} 2^{n-3k-4} +
\binom{n-k-4}{2k-1} 2^{n-3k-3} \right) + 2^{n-4} = F_{2n-7}.$$

The sum is empty for $n < 6$. When $3$ divides $n$, the last index $k = n/3 - 1$ gives the
exponent $n - 3k - 4 = -1$, but there $\binom{n-k-4}{2k} = 0$, and the product
$\binom{n-k-4}{2k} 2^{n-3k-4}$ is read as $0$; the other product in that summand is $1$.

The source states this as the sum being $F_{2n-7} - 2^{n-4}$. The summand is reconstructed from
an extracted display of the source's Proposition 2(i), as the full text was not available; exact
computation confirms the identity for $4 \le n \le 500$.

## Sources

- David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Proposition 3, with the sum of Proposition 2(i).
