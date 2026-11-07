# Metered parking functions in which every car is lucky

Let $m \ge 2$, $n \ge 2$ and
$t \le m - 1$. The number of $t$-metered $(m, n)$-parking functions in which every car parks in
its preferred spot is $n(n-1)\cdots(n-t+1) \cdot (n-t)^{m-t}$, where the falling factorial
$n(n-1)\cdots(n-t+1)$ has $t$ factors (it equals $1$ for $t = 0$ and $0$ for $t > n$).

The source's companion formula (12) for exactly one lucky car is not stated: it is false as
printed when $m > n + 1$ (for $n = 2$, $m = 4$, $t = 1$ the count is $0$, while the formula
$(t-1)!\,(n-m+1)\,t^{m-t}$ gives $-1$).

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Proposition 8, Equation (13) (`integers-2025-A73-prop-8`).
