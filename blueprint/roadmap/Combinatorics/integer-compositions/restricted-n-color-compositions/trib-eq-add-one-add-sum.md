# Tribonacci numbers from $t(n-1)$ and alternate earlier terms

Let $t$ be the tribonacci
numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for
$n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every integer $n \ge 3$,

$$t(n) = t(n-1) + 1 + 2 \sum_{i=1}^{\lfloor n/2 \rfloor - 1} t(n-2i-1).$$

## Sources

- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Proposition 7.
