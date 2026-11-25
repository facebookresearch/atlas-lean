# Last-to-root move on an array

For a nonempty array $a = (a_0, \dots, a_{n-1})$, the
last-to-root move swaps $a_0$ and $a_{n-1}$ and then deletes the last entry, producing an array
$b = (b_0, \dots, b_{n-2})$ of length $n - 1$: when $n \ge 2$, $b_0 = a_{n-1}$ and
$b_i = a_i$ for $0 < i < n - 1$, and $b$ is empty when $n = 1$.
