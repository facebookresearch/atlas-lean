# Josephus survivor function

For natural numbers $k$ and $n$, the Josephus function
$J_k(n)$ is defined by recursion on $n$: $J_k(0) = 0$ and
$J_k(n+1) = ((J_k(n) + k - 1) \bmod (n+1)) + 1$, where subtraction of natural numbers is
truncated at $0$.

For $k \ge 2$ and $n \ge 1$, $J_k(n)$ is the one-based position of the sole survivor when every
$k$-th person is eliminated from a circle of $n$ people; the value $J_k(0) = 0$ only anchors the
recursion.

## Sources

- concept `jis_sem_e1c9a353312d2a1564410d6e`; source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`, `jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`, `jis_fe4f24c64ecfdad23577e877`; clauses `domain`, `meaning`.
