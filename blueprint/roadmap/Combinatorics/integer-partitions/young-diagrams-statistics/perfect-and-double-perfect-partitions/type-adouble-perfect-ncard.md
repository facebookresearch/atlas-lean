# Number of Type-A double-perfect partitions

Let $f(n)$ be the number of ordered
factorizations of $n$ into factors greater than $1$. Let $r \ge 1$ and $N \ge 2(r+1)$, that is,
$1 \le r \le \lfloor (N-2)/2 \rfloor$, and put $M = 2(r+1)$. The number $d_r(N)$ of Type-A
double-perfect partitions of $N$ of order $r$ is
$f(N-r) - f((N-r)/M) - (f(r+1) - 1) f((N-r)/(r+1))$ if $N \equiv r \pmod M$,
$f(N-r) - (f(r+1) - 1) f((N-r)/(r+1))$ if $N \equiv -1 \pmod M$, and $f(N-r)$ otherwise.

## Sources

- Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025), Article A109, Theorem 3, display (18) (`integers-2025-A109-thm-3`).
