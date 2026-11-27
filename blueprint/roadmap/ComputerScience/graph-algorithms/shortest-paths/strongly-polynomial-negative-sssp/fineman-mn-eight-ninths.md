# Fineman's randomized O~(m n^{8/9}) algorithm for real-weighted single-source shortest paths

There is a Las Vegas randomized algorithm in the real RAM that, given a directed graph with $n$ vertices, $m$ edges, real edge lengths and a source $s$, either reports a negative cycle or computes all distances from $s$, and terminates in $\tilde O(mn^{8/9})$ time with high probability. Its core step, on a graph with $k$ remaining negative edges and parameter $r=\Theta(k^{1/9})$, computes in $\tilde O(k^{2/9}m)$ time a valid price function neutralizing $\Theta(k^{1/3})$ negative edges (or finds a negative cycle). This is the first asymptotic improvement over the $O(mn)$ bound of Bellman-Ford-Moore-Shimbel for real weights.

## Proof sketch

One iteration performs betweenness reduction with $\beta=r+1,\tau=r$ in $\tilde O(r^2m)$ time, then finds a size-$\Omega(k^{1/3})$ negative sandwich or $1$-hop independent set; an independent set is neutralized directly, while a sandwich is reweighted to be $r$-remote and eliminated by hop reduction in $\tilde O((k^{1/3}/r)m+rm)$ time, restarting if betweenness reduction failed. The cost $\tilde O(m(r^2+k^{1/3}/r))$ is minimized at $r=\Theta(k^{1/9})$, giving $\tilde O(k^{2/9}m)$ per $\Theta(k^{1/3})$ neutralized edges. Halving $k$ takes $O(k^{2/3})$ iterations, i.e. $\tilde O(k^{8/9}m)$ time, and summing the geometric series from $k\le n$ gives $\tilde O(mn^{8/9})$.

## Depends on

- [Real-weighted negative SSSP in the real RAM and strongly polynomial running time](real-weighted-sssp-strongly-polynomial.md)

## Proof depends on

- [Eliminating r-remote negative edges by hop reduction in O~((k/r)m + rm) time](remote-edge-elimination.md)
- [Betweenness reduction: one reweighting makes every pair have beta-betweenness at most n/tau](betweenness-reduction-by-sampling.md)
- [A negative sandwich with low-betweenness endpoints becomes r-remote after one valid reweighting](negative-sandwich-becomes-remote.md)
- [Finding a negative sandwich or a 1-hop independent set of size Omega(k^{1/3}) in O(m log^2 n) time](sandwich-or-independent-set-sampling.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
