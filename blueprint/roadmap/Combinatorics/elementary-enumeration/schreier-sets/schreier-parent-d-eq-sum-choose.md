# Binomial sum formula for the parent sequence

For all natural numbers $u \ge 2$ and
$n \ge 1$, the parent sequence $d_{u,n}$ satisfies

$$
d_{u,n} = \sum_{i=0}^{\lfloor (n-1)/u \rfloor} \binom{\lfloor (n + (u-1)i - u)/(2u-1) \rfloor}{i}.
$$

The numerator $n + (u-1)i - u$ is negative only when $i = 0$ and $n < u$. There it is read as
$0$ (truncated subtraction), so the term is $\binom{0}{0} = 1$, which agrees with the paper's
$\binom{-1}{0} = 1$.

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Proposition 2.
