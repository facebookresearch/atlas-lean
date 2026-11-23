# The parent sequence $d_{u,n}$

For natural numbers $u$ and $n$, define $d_{u,n}$ by
recursion on $n$: $d_{u,n} = 1$ if $n < 2u$ or $u = 0$, and otherwise
$d_{u,n} = d_{u,n-u} + d_{u,n-2u+1}$.

The paper takes $u \ge 2$ and indexes from $n = 1$, with $d_{u,n} = 1$ for $1 \le n \le 2u - 1$;
the definition above also gives $d_{u,0} = 1$, and $d_{0,n} = 1$ for every $n$ in the degenerate case $u = 0$.

## Sources

- Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026), Article A53, Section 4 (definition of `d_{u,n}`).
