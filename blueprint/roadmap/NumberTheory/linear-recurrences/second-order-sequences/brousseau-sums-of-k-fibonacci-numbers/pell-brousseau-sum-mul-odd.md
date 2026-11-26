# Power-weighted Pell sums along odd multiples

Let $P_n$ be the Pell numbers and $Q_n$ the
Pell–Lucas numbers, the Lucas sequence $V(2, -1)$: $Q_0 = Q_1 = 2$ and
$Q_{n+2} = 2 Q_{n+1} + Q_n$. Let $m$ be an odd natural number and write $k = Q_m$. Let
$A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$, and let $C_k^{(p)}(x) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} x^{p-r}$, with
$0^0 = 1$. Then for all natural numbers $n$ and $p$,

$$
Q_m \sum_{i=1}^{n} i^p P_{mi} = C_k^{(p)}(n) P_{m(n+1)} + C_k^{(p)}(n+1) P_{mn} -
C_k^{(p)}(0) P_m.
$$

## Sources

- Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*, Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 10 (`jis-2024-24.6.4-cor-10`).
