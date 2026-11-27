# Deterministic near-linear minimum cut in weighted graphs (Henzinger-Li-Rao-Wang)

There is a deterministic algorithm that computes a global minimum cut of a connected undirected graph with $n$ vertices, $m$ edges and positive integer weights bounded by $n^{O(1)}$ in $O(m \log^{c} n)$ time for an absolute constant $c$. This matches, up to the polylogarithmic factor, the randomized $O(m \log^3 n)$ bound of Karger.

## Proof sketch

The main structural result is that every weighted graph has a sparse clustering whose contraction preserves all minimum cuts up to a $1 + o(1/\log n)$ factor, constructed deterministically in near-linear time by extending the Kawarabayashi-Thorup and Henzinger-Rao-Wang local-flow trimming to weighted graphs with polylogarithmic error and then sharpening the error using tree packings to locate sources for local flow computations. Applied recursively over $O(\log n)$ levels as in Li's framework, the clusterings produce polylogarithmically many spanning trees one of which $2$-respects the minimum cut, and the deterministic $2$-respecting algorithm finishes.

## Depends on

- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [Deterministic almost-linear minimum cut in weighted graphs (Li)](li-deterministic-almost-linear-weighted-mincut.md)
- [Deterministic near-linear edge connectivity of simple graphs](deterministic-edge-connectivity-simple-graphs.md)
- [Minimum 2-respecting cut of a spanning tree in O(m log n) deterministic time](minimum-two-respecting-cut-algorithm.md)
- [Kawarabayashi-Thorup contraction to O(m/delta) edges preserving non-trivial minimum cuts](kawarabayashi-thorup-contraction.md)

## Sources

- Monika Henzinger, Jason Li, Satish Rao, Di Wang, "Deterministic Near-Linear Time Minimum Cut in Weighted Graphs", SODA (2024), arXiv:2401.05627.
- Jason Li, "Deterministic Mincut in Almost-Linear Time", STOC (2021), arXiv:2106.05513.
- Ken-ichi Kawarabayashi, Mikkel Thorup, "Deterministic Edge Connectivity in Near-Linear Time", STOC (2015) and Journal of the ACM (2019), arXiv:1411.5123.
- Monika Henzinger, Satish Rao, Di Wang, "Local Flow Partitioning for Faster Edge Connectivity", SODA (2017) and SIAM Journal on Computing (2020), arXiv:1704.01254.
