# Josephus survivor function

For natural numbers $k$ and $n$, the Josephus function
$J_k(n)$ is defined by recursion on $n$: $J_k(0) = 0$ and
$J_k(n+1) = ((J_k(n) + k - 1) \bmod (n+1)) + 1$, where subtraction of natural numbers is
truncated at $0$.

For $k \ge 2$ and $n \ge 1$, $J_k(n)$ is the one-based position of the sole survivor when every
$k$-th person is eliminated from a circle of $n$ people; the value $J_k(0) = 0$ only anchors the
recursion.
