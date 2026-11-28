# Offsets of final terms of comma sequences in danger intervals

For natural numbers $b$ and $d$, $U(b, d)$ is the set of numbers $u = rb + s$ with digits $r, s < b$ such that, when $d = 1$, $s > 0$ and $r + s \le b$, and when $d \ne 1$, either $s > 0$ and $r + s < b$, or $r + s = b$ and $s < d$. The digit formula is defined for all $b$ and $d$. Its elements are offsets, not the final terms themselves: for $b \ge 2$, $1 \le d < b$ and $k > 2$ (see the [characterization of final values in danger intervals](comma-danger-final-iff-mem.md)), a final term in the danger interval $[d b^k - b^2, d b^k)$ is $d b^k - u$ with $u \in U(b, d)$. Outside that domain the reading can fail: for $b = 3$, $d = 4$ and $k = 1$ the term $4$ is final but its offset $8$ is not in $U(3, 4)$; for $b = 3$, $d = 1$ and $k = 3$, the offset $1 \in U(3, 1)$ gives the final term $26 \in [18, 27)$.

## Sources

- R. Dougherty-Bliss and N. Ter-Saakov, The comma sequence is finite in other bases, J. Integer Seq. 28 (2025), Article 25.5.5.
