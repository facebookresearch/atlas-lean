# Ordinary moment recurrence

Let $b$ and $d$ be natural numbers, and for $i \ge 1$ let
$\gamma_i$ be the sum of the $i$-th powers of the base-$b$ digits $a \in \{0, \dots, b-1\}$ with
$a \ne d$. A family of real numbers $(u_{j;m})_{j, m \in \mathbb{N}}$ satisfies the ordinary
moment recurrence for $b$ and $d$ when $u_{0;0} = b$, when for every $m \ge 1$

$$
(b^{m+1} - b + 1)\, u_{0;m} = \sum_{i=1}^{m} \binom{m}{i} \gamma_i\, u_{0;m-i},
$$

and when for every $j \ge 1$ and every $m \ge 0$

$$
(b^{m+1} - b + 1)\, u_{j;m} = \sum_{i=1}^{m} \binom{m}{i} \gamma_i\, u_{j;m-i} +
\sum_{i=0}^{m} \binom{m}{i} d^i\, u_{j-1;m-i}.
$$

## Sources

- Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 1.
