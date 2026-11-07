# Zone factorization of the $m$-level rook polynomial

Let $m \ge 1$ and let
$B = (b_1, \dots, b_n)$ be a Ferrers board, that is $b_1 \le \dots \le b_n$. Write
$\lfloor b \rfloor_m = m \lfloor b/m \rfloor$ for the largest multiple of $m$ that is at most $b$,
and $\rho_i = b_i - \lfloor b_i \rfloor_m$. The zone of column $i$ is the set $z$ of columns $k$
with $\lfloor b_k \rfloor_m = \lfloor b_i \rfloor_m$ (a maximal run of consecutive columns, since
the heights increase weakly), and $\rho_z = \sum_{k \in z} \rho_k$. Column $i$ is last in its zone
when $i = n$ or $\lfloor b_{i+1} \rfloor_m \ne \lfloor b_i \rfloor_m$. Let $\varepsilon_i = \rho_z$,
for $z$ the zone of $i$, if column $i$ is last in its zone, and $\varepsilon_i = 0$ otherwise.
Then for every integer $x$,

$$
\sum_{k=0}^{n} r_{k,m}(B)\, x\downarrow_{n-k,m} =
\prod_{i=1}^{n} \bigl(x + \lfloor b_i \rfloor_m - m(i-1) + \varepsilon_i\bigr),
$$

where $r_{k,m}(B)$ is the $k$-th $m$-level rook number of $B$ and
$x\downarrow_{k,m} = x(x-m)\cdots(x-(k-1)m)$ is the $m$-falling factorial.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Theorem 3 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-3`).
