# Weighted file numbers equal level rook numbers on singleton boards

Let $m \ge 1$ and let
$B$ be a singleton board for $m$. Then for every $k \in \mathbb{N}$ the $k$-th $m$-weighted file
placement number of $B$ equals its $k$-th $m$-level rook number: $f_{k,m}(B) = r_{k,m}(B)$.

Equivalently, the $m$-weights of the file placements with $k$ cells that are not $m$-level rook
placements sum to $0$. The paper prints the corollary as the polynomial identity
$\sum_k f_{k,m}(B)\, x\downarrow_{n-k,m} = \sum_k r_{k,m}(B)\, x\downarrow_{n-k,m}$, where $n$ is
the number of columns and $x\downarrow_{j,m} = \prod_{i\lt j} (x - mi)$; it follows by summing, and the
paper derives it from this cancellation for each $k$.

## Sources

- Kenny Barrese, *Weighted File Placements on Singleton Boards*, INTEGERS 24 (2024), Article A58, Corollary 6 and the sentence before it.
