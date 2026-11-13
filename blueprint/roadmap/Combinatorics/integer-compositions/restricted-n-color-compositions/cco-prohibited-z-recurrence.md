# Recurrence for n-color compositions avoiding two consecutive colors

Fix a natural number
$b \ge 1$. For an integer $m$, let $c(m)$ be the number of $n$-color compositions of $m$ in
which no part has color $b$ or $b+1$ when $m \ge 0$, and $c(m) = 0$ when $m < 0$. Then for
every integer $n \ge 3$,

$$c(n) = 3\,c(n-1) - c(n-2) - c(n-b) + c(n-b-2).$$

The source states the recurrence without a range, but it fails at $n = 0$, $1$ and $2$.

## Sources

- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Proposition 11.
