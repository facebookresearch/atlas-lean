# Inverse Ackermann function of Tarjan and van Leeuwen

For natural numbers $m$ and $n$, $\alpha(m, n)$ is the least $i \ge 1$ such that
$A(i, \lfloor m/n \rfloor) > L(n)$, where $A$ is
[Tarjan and van Leeuwen's Ackermann function](ackermann-tv-l.md), $L(n) = \lfloor \log_2 n \rfloor$
for $n \ge 1$, $L(0) = 0$ and $\lfloor m/0 \rfloor = 0$; if no such $i$ exists, $\alpha(m, n) = 0$.
Since $A(i, j)$ is an integer, $A(i, j) > \lfloor \log_2 n \rfloor$ is equivalent to
$A(i, j) > \log_2 n$ when $n \ge 1$, so for $m \ge n \ge 1$ this is Tarjan and van Leeuwen's

$$\alpha(m, n) = \min\{\, i \ge 1 : A(i, \lfloor m/n \rfloor) > \log_2 n \,\}.$$

When $\lfloor m/n \rfloor = 0$, that is, when $m < n$ or $n = 0$, only $i = 1$ can qualify,
since $A(1, 0) = 1$ and $A(i, 0) = 0$ for $i \ge 2$: so $\alpha(m, n) = 1$ if $n \le 1$, and
$\alpha(m, n) = 0$ if $m < n$ and $n \ge 2$ (for example $\alpha(0, 2) = 0$). The function grows extremely slowly: $\alpha(m, n) \le 3$
for $n < 2^{16}$.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §1, definition of $\alpha$ and Remarks 2–3.
