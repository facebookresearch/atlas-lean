# Recurrence for n-color compositions with two consecutive colors

Fix a natural number
$b \ge 1$. For an integer $m$, let $c(m)$ be the number of $n$-color compositions of $m$ in
which every part has color $b$ or $b+1$ when $m \ge 0$, and $c(m) = 0$ when $m < 0$. Then for
every integer $n \ge 2$,

$$c(n) = c(n-1) + c(n-b) + c(n-b-1).$$

The source states the recurrence for positive $n$, but it fails at $n = 1$: for $b = 1$ the
left side is $1$ and the right side is $2$.

## Sources

- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Proposition 1.
