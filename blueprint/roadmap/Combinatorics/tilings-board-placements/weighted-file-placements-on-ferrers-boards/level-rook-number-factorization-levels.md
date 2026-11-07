# Level-number factorization of the $m$-level rook polynomial

Let $m \ge 1$ and let
$B = (b_1, \dots, b_n)$ be a Ferrers board, that is $b_1 \le \dots \le b_n$, with $b_i \le mn$ for
every $i$. Number the rows from $0$ at the bottom, so that column $i$ has the cells in rows
$0, \dots, b_i - 1$, and for $1 \le j \le n$ let $l_j$ be the number of cells of $B$ whose row $r$
satisfies $\lfloor r/m \rfloor = n - j$ (the $j$-th level from the top). Then for every integer $x$,

$$
\sum_{k=0}^{n} r_{k,m}(B)\, x\downarrow_{n-k,m} = \prod_{j=1}^{n} \bigl(x + l_j - m(j-1)\bigr),
$$

where $r_{k,m}(B)$ is the $k$-th $m$-level rook number of $B$ and
$x\downarrow_{k,m} = x(x-m)\cdots(x-(k-1)m)$ is the $m$-falling factorial.

The bound $b_i \le mn$ makes $B$ lie in $n$ levels, as in the paper's setting; without it the
formula fails ($m = 1$, $B = (2)$).

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Theorem 4 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-4`).
