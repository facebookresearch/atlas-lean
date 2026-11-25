# Cache-oblivious scanning and matrix transposition

In the ideal-cache model with cache size $Z$ and line length $L$: scanning $n$ contiguous words incurs at most $\lceil n/L \rceil + 1$ cache misses for any $Z \ge L$. Under the tall-cache assumption $Z = \Omega(L^2)$, the cache-oblivious algorithm that transposes an $m \times n$ row-major matrix by recursively halving the larger dimension incurs $O(1 + mn/L)$ cache misses, and for $m, n \ge 1$ this is $\Theta(1 + mn/L)$, which is optimal.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th IEEE FOCS*, 1999
