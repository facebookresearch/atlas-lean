# Parent sequence b for Schreier-type multisets

For natural numbers $s$ and $p$, the
sequence $b^{(s)}_{p,n}$, $n \ge 0$, is defined by $b^{(s)}_{p,n} = 0$ for $n \le (p - 1)s$,
$b^{(s)}_{p,n} = 1$ for $(p - 1)s < n \le ps + 1$, and
$b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for $n \ge ps + 2$, where $p - 1$ is read
as $0$ when $p = 0$.

The paper indexes from $n = 1$; here $b^{(s)}_{p,0} = 0$.

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Section 3 (definition of `b^{(s)}_{p,n}`).
