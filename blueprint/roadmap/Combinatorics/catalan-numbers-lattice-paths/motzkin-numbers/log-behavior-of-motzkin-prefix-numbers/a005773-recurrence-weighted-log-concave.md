# Log-concave weighted sequences built from A005773

Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$\Delta A_n = A_{n+1} - A_n$ and $\Delta^2 A_n = A_{n+2} - 2A_{n+1} + A_n$. Then for every
$n \ge 2$, each of the four sequences $z_m = m A_m$, $z_m = (m+1) A_{m+1} - m A_m$,
$z_m = m\,\Delta A_m$ and $z_m = m\,\Delta^2 A_m$ satisfies $z_{n-1} z_{n+1} \le z_n^2$. That
is, these four sequences, indexed from $m = 1$, are log-concave.

## Sources

- Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence Sequence*, INTEGERS 25 (2025), Article A100, Theorem 3.
