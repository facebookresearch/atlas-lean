# The alternating Motzkin sums are eventually log-balanced and tempered

Let $M_k$ denote
the $k$-th Motzkin number and let $T_n = \sum_{k=0}^{n} (-1)^{n-k} M_k$. For every natural
number $n \ge 9$,

$$T_n^2 \le T_{n-1} T_{n+1} \quad\text{and}\quad n T_{n-1} T_{n+1} \le (n+1) T_n^2,$$

and for every natural number $n \ge 6$,

$$n T_n^2 \le (n+1) T_{n-1} T_{n+1} \quad\text{and}\quad n T_{n-1} T_{n+1} \le (n+1) T_n^2.$$

Following Došlić, a positive sequence $(z_n)_{n \ge N}$ is log-balanced if it is log-convex,
$z_n^2 \le z_{n-1} z_{n+1}$, and $(z_n/n!)$ is log-concave, $n z_{n-1} z_{n+1} \le (n+1) z_n^2$,
for every $n \ge N + 1$; it is tempered if its quotients $x_n = z_{n+1}/z_n$ satisfy
$\frac{n}{n+1} x_{n-1} \le x_n \le \frac{n+1}{n} x_{n-1}$ for every $n \ge N + 1$. So the two
parts say that $(T_n)_{n \ge 8}$ is log-balanced and $(T_n)_{n \ge 5}$ is tempered, with the
inequalities cleared of denominators (all terms are positive here) and the factorials and
quotient weights using the original index $n$, as in the paper's proofs.

## Sources

- Feng-Zhen Zhao, *The Log-Balancedness of the Sequence for the Alternating Sums of Motzkin Numbers*, INTEGERS 26 (2026), Article A55, Theorem 1.
