# Deterministic near-linear edge connectivity of simple graphs

There is a deterministic algorithm that, given a simple connected undirected graph with $n$ vertices and $m$ edges, computes its edge connectivity $\lambda$ together with a global minimum cut in $O(m \log^{12} n)$ time (Kawarabayashi-Thorup), improved to $O(m \log^2 n (\log\log n)^2)$ time (Henzinger-Rao-Wang). Within near-linear deterministic time the cactus representation of all minimum cuts can also be constructed. For comparison, randomized algorithms achieve $O(m \log n)$ and $O(m + n \log^3 n)$ time with high probability (Ghaffari-Nowicki-Thorup).

## Proof sketch

If $\delta$ is at most polylogarithmic, Gabow's $\tilde O(\lambda m)$ algorithm suffices because $\lambda \le \delta$. Otherwise contract a partition preserving all non-trivial minimum cuts to obtain a multigraph with $\tilde O(m/\delta)$ edges, run Gabow's algorithm there in $\tilde O(\lambda m / \delta) = \tilde O(m)$ time, and compare the result with the minimum degree, which accounts for the trivial cuts. Henzinger-Rao-Wang obtain the contraction faster by replacing diffusion-based low-conductance cut finding with local flow partitioning.

## Depends on

- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [Kawarabayashi-Thorup contraction to O(m/delta) edges preserving non-trivial minimum cuts](kawarabayashi-thorup-contraction.md)

## Sources

- Ken-ichi Kawarabayashi, Mikkel Thorup, "Deterministic Edge Connectivity in Near-Linear Time", STOC (2015) and Journal of the ACM (2019), arXiv:1411.5123.
- Monika Henzinger, Satish Rao, Di Wang, "Local Flow Partitioning for Faster Edge Connectivity", SODA (2017) and SIAM Journal on Computing (2020), arXiv:1704.01254.
- Mohsen Ghaffari, Krzysztof Nowicki, Mikkel Thorup, "Faster Algorithms for Edge Connectivity via Random 2-Out Contractions", SODA (2020), arXiv:1909.00844.
