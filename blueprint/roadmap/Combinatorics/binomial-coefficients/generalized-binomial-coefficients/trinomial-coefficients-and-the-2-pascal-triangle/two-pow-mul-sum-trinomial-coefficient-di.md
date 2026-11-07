# Weighted diagonal sums of trinomial coefficients and the sequence A075115

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. Let
$(\lambda_m)$ be the integer sequence with $\lambda_0 = 3$, $\lambda_1 = 2$, $\lambda_2 = 0$ and
$\lambda_{m+3} = 2\lambda_{m+2} - 2\lambda_{m+1} + 2\lambda_m$ (OEIS A075115). For every natural
number $n \ge 1$,
$2^n \sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} = \lambda_{3n}$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 33 (`jis-2025-25.3.5-cor-33`).
