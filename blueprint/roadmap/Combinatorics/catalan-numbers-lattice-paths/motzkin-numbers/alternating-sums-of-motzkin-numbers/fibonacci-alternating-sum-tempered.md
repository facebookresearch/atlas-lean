# The alternating Fibonacci sums are eventually tempered

Let $F_k$ denote the $k$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, and let $W_n = \sum_{k=0}^{n} (-1)^{n-k} F_k$.
For every natural number $n \ge 12$,

$$n W_n^2 \le (n+1) W_{n-1} W_{n+1} \quad\text{and}\quad n W_{n-1} W_{n+1} \le (n+1) W_n^2.$$

These are the conditions $\frac{n}{n+1} x_{n-1} \le x_n \le \frac{n+1}{n} x_{n-1}$ on the
quotients $x_n = W_{n+1}/W_n$, cleared of denominators (all terms are positive here), so the
sequence $(W_n)_{n \ge 11}$ is tempered, with the conditions imposed at every index $n \ge 12$.

## Sources

- Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 4.
