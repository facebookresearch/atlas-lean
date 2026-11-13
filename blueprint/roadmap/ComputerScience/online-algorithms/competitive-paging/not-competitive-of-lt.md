# No deterministic online pager is better than $k$-competitive

Let $k \ge 1$ and let $A$
be a deterministic online pager with cache size $k$ on the $k + 1$ pages $0, \dots, k$. For a
request sequence $\sigma$, write $A(\sigma)$ for the number of misses of $A$ started in its
initial state on $\sigma$, and $\mathrm{OPT}(\sigma)$ for the number of misses of the
furthest-in-future strategy with capacity $k$ started with an empty cache on $\sigma$. Then for
all natural numbers $c$, $d$ with $c < kd$ and every natural number $b$, there is a request
sequence $\sigma$ with $c \cdot \mathrm{OPT}(\sigma) + b < d \cdot A(\sigma)$. That is, the pager
misses more than $c / d$ times the optimum plus $b / d$.
