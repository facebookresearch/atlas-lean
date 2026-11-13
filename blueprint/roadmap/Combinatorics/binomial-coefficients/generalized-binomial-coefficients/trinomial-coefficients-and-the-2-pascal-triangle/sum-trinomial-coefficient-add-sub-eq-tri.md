# Tribonacci formula for a diagonal sum of trinomial coefficients

Write $\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in
$(1 + t + t^2)^n$, and $T_n$ for the Tribonacci numbers, $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$. Then for every $n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \binom{n + k}{n - k}_2 = \frac{T_{2(n+1)}}{2} + \frac{1}{2}\binom{n}{n}_2 +
\frac{1}{2} \sum_{k=0}^{n-1} \binom{k}{k}_2 \left(T_{2(n-k)} + T_{2(n-1-k)}\right).$$

The sequence $(T_{2n})$ is the bisection A099463.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 42 (`jis-2025-25.3.5-cor-42`).
