# Initial segments of the Fibonacci $m$-step sequence

For natural numbers $m$ and $n$,
this is the list of integers $[F_0, F_1, \dots, F_n]$, built recursively: the list for $n = 0$
is $[0]$, the list for $n = 1$ is $[0, 1]$, and for $n \ge 2$ the list for $n$ is the list for
$n - 1$ followed by $F_n = \sum_{j=1}^{m} F_{n-j}$, where $F_i = 0$ for $i < 0$.
