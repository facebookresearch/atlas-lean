# Real-weighted SSSP in O(m n^{4/5} log^{2/5} n + n^{9/5} log^{7/5} n) randomized time via proper hop distances

There is a Las Vegas randomized algorithm that solves the real-weighted SSSP problem (returning a negative cycle or all distances from $s$) on a directed graph with $n$ vertices and $m$ edges in

$$
O\big(mn^{4/5}\log^{2/5}n+n^{9/5}\log^{7/5}n\big)
$$

time with high probability.

## Proof sketch

With $k$ negative vertices, set $h=k^{1/5}/\log^{2/5}n$ and reduce the $O(h)$-betweenness of all pairs to $n/h$ in $O(h^2(m\log n+n\log^2 n))$ time. The proper-hop sampling step then either neutralizes $\Omega(\sqrt{hk})$ negative vertices directly or returns a weak $h$-hop sandwich of that size, which is made $h$-remote and eliminated by hop reduction in $O((h+\ell/h)(m+n\log n))$ time. Thus $\ell=\Omega(\sqrt{kh})$ edges are neutralized in $O((h^2\log n+\ell/h)(m+n\log n))$ time; halving the number of negative vertices dominates, and the total is $O((n^{1/2}h^{3/2}\log n+n/h)(m+n\log n))$, which gives the stated bound.

## Depends on

- [Real-weighted negative SSSP in the real RAM and strongly polynomial running time](real-weighted-sssp-strongly-polynomial.md)

## Proof depends on

- [Proper h-hop walks yield weak h-hop negative sandwiches of size Omega(sqrt(hk))](proper-hop-walks-and-weak-sandwiches.md)
- [Eliminating r-remote negative edges by hop reduction in O~((k/r)m + rm) time](remote-edge-elimination.md)
- [Betweenness reduction: one reweighting makes every pair have beta-betweenness at most n/tau](betweenness-reduction-by-sampling.md)

## Sources

- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
