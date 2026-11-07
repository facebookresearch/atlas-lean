# Binet formula for decimated linear recurrences

Let $m$ and $r$ be natural numbers and
let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be sequences of complex numbers such that
$s_{n+mr} = \sum_{j\lt m} A_j s_{n+jr}$ for all $n \ge 0$. Let $f(x) = x^m - \sum_{j\lt m} A_j x^j$
and let $\alpha_1, \ldots, \alpha_m$ be pairwise distinct roots of $f$ in $\mathbb{C}$. Then
for every $n \ge 0$

$$
s_n = \sum_{l\lt m} v_l^{(n \bmod r)}
\sum_{t=1}^{m} \frac{\alpha_t^{m-1-l+\lfloor n/r \rfloor}}{f'(\alpha_t)},
$$

where $v_l^{(i)} = s_{lr+i} - \sum_{j\lt l} A_{m-1-j} s_{(l-1-j)r+i}$ are the decimation
coefficients. For $r = 0$ the formula is read with $n \bmod 0 = n$ and
$\lfloor n/0 \rfloor = 0$.

## Sources

- Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 2 (`integers-2026-A5-thm-2`).
