# Cache-oblivious matrix multiplication

In the [ideal-cache model](the-ideal-cache-model.md) with a cache of $Z$ words and lines of $L$ words satisfying the tall-cache assumption $Z = \Omega(L^2)$, with matrices stored in row-major order, the cache-oblivious algorithm REC-MULT multiplies an $m \times n$ matrix by an $n \times p$ matrix with $\Theta(mnp)$ work and

$$
O\bigl(m + n + p + (mn + np + mp)/L + mnp/(L\sqrt Z)\bigr)
$$

cache misses. The source states this count with $\Theta$, but in this layout it is only an upper bound: for $m = p = 1$, $n = 4L$ and $Z$ a large multiple of $L^2$, the two vectors and the result occupy a constant number of cache lines and REC-MULT incurs $O(1)$ misses, not $\Omega(n)$. REC-MULT halves the largest of the three dimensions and recurs: if $m \ge \max(n, p)$ it splits $A$ horizontally, if $n \ge \max(m, p)$ it splits $A$ vertically and $B$ horizontally and adds the two products, and otherwise it splits $B$ vertically.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 2, the algorithm REC-MULT (equations (2)–(4)) and Theorem 1, with the tall-cache assumption (1) required there for row-major layout.
