# The third differences of A005773 are log-convex and log-balanced

Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$z_n = \Delta^3 A_n = A_{n+3} - 3A_{n+2} + 3A_{n+1} - A_n$. Then $z_n^2 \le z_{n-1} z_{n+1}$
for every $n \ge 3$, and

$$\frac{z_{n-1}}{(n-1)!} \cdot \frac{z_{n+1}}{(n+1)!} \le \left(\frac{z_n}{n!}\right)^2$$

for every $n \ge 4$. That is, $(\Delta^3 A_n)_{n \ge 2}$ is log-convex and
$(z_n / n!)_{n \ge 3}$ is log-concave, so $(\Delta^3 A_n)_{n \ge 3}$ is log-balanced.

## Sources

- Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence Sequence*, INTEGERS 25 (2025), Article A100, Theorem 2.
