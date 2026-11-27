# Complementary moment recurrence

Let $b$ and $d$ be natural numbers, let $d' = b - 1 - d$
(natural-number subtraction), and let $\gamma'_i$ be the complementary digit power sum for $b$ and
$d$. A family $(v_{j,m})_{j, m \ge 0}$ of real numbers satisfies the complementary moment
recurrence when, for every $m \ge 0$,

$$
(b^{m+1} - b + 1)\, v_{0,m} = b^{m+1} + \sum_{i=1}^{m} \binom{m}{i} \gamma'_i \, v_{0,m-i},
$$

and, for every $j \ge 1$ and every $m \ge 0$,

$$
(b^{m+1} - b + 1)\, v_{j,m} = \sum_{i=1}^{m} \binom{m}{i} \gamma'_i \, v_{j,m-i} +
\sum_{i=0}^{m} \binom{m}{i} (d')^i \, v_{j-1,m-i},
$$

with the convention $0^0 = 1$.

## Sources

- Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 2.
