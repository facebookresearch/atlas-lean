# Factorization theorem for weighted file placements

Let $m \ge 1$ and let $B$ be a Ferrers
board with $n$ columns of weakly increasing heights $b_0 \le b_1 \le \dots \le b_{n-1}$ (columns
indexed from $0$). Then for every integer $x$,

$$\sum_{k=0}^{n} f_{k,m}(B)\, x\downarrow_{n-k,m} = \prod_{i=0}^{n-1} (x + b_i - mi),$$

where $f_{k,m}(B)$ is the $k$-th $m$-weighted file placement number of $B$ and
$x\downarrow_{j,m} = \prod_{i\lt j} (x - mi)$ is the $m$-falling factorial.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Theorem 5 (Barrese, Loehr, Remmel and Sagan) (`integers-2024-A58-thm-5`).
