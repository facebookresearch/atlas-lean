# The first and second differences of A005773 are log-balanced

Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$\Delta A_n = A_{n+1} - A_n$ and $\Delta^2 A_n = A_{n+2} - 2A_{n+1} + A_n$. Then for every
$n \ge 4$, each of the sequences $z = \Delta A$ and $z = \Delta^2 A$ satisfies
$z_n^2 \le z_{n-1} z_{n+1}$ and

$$\frac{z_{n-1}}{(n-1)!} \cdot \frac{z_{n+1}}{(n+1)!} \le \left(\frac{z_n}{n!}\right)^2.$$

That is, $(\Delta A_n)_{n \ge 3}$ and $(\Delta^2 A_n)_{n \ge 3}$ are log-balanced: log-convex, with
$(z_n / n!)_{n \ge 3}$ log-concave.

## Sources

- Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence Sequence*, INTEGERS 25 (2025), Article A100, Theorem 1.
