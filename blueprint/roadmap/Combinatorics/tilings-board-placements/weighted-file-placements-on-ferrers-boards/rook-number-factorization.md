# Goldman–Joichi–White factorization theorem

Let $B = (b_1, \dots, b_n)$ be a Ferrers
board, that is $b_1 \le \dots \le b_n$, and let $r_k(B) = r_{k,1}(B)$ be the number of placements
of $k$ non-attacking rooks on $B$ (no two in the same row or column). Then for every integer $x$,

$$
\sum_{k=0}^{n} r_k(B)\, x\downarrow_{n-k} = \prod_{i=1}^{n} \bigl(x + b_i - (i-1)\bigr),
$$

where $x\downarrow_j = x(x-1)\cdots(x-j+1)$ is the falling factorial, the $m$-falling factorial
for $m = 1$.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Theorem 1 (Goldman, Joichi and White) (`integers-2024-A58-thm-1`).
