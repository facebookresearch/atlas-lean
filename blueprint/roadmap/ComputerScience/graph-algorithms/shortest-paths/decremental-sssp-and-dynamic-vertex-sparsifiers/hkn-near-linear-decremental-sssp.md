# Henzinger-Krinninger-Nanongkai: decremental SSSP in m^{1+o(1)} total update time via hopsets

For undirected graphs with integer edge weights in $[1, W]$ and $0 < \varepsilon \le 1$ with $1/\varepsilon = \mathrm{polylog}(n)$ (constant $\varepsilon$ included), there is a randomized decremental $(1+\varepsilon)$-approximate SSSP data structure with constant query time and expected total update time $O(m^{1 + o(1)}\log W + n)$, against an oblivious adversary, whose distance estimates are correct with high probability (FOCS version and arXiv v1, Section 1: "it is correct with high probability and the bound on its total update time holds in expectation"). The journal version (Section 1) strengthens this to an algorithm that is always correct, a Las Vegas algorithm. The algorithm maintains a sparse $(h, \varepsilon)$-hopset $F$, a set of weighted edges such that for all $u, v$,

$$
\mathrm{dist}_G(u, v) \le \mathrm{dist}^{(h)}_{G \cup F}(u, v) \le (1 + \varepsilon)\,\mathrm{dist}_G(u, v),
$$

where $\mathrm{dist}^{(h)}$ is the minimum length of a path with at most $h$ edges and $h = n^{o(1)}$.

## Proof sketch

On $G \cup F$, distances are realized by paths with few hops, so a weighted, rounded variant of the Even-Shiloach tree that only tracks $h$-hop distances runs in time about $m h$ per distance scale. The hopset is built from a hierarchy of balls around randomly sampled centres, which is decremental-friendly because balls only shrink; its edges are maintained by Even-Shiloach trees of bounded depth. The random centres must not be revealed to the adversary, which is why the guarantee assumes obliviousness.

## Depends on

- [Decremental (1+eps)-approximate single-source shortest paths](decremental-approximate-sssp-problem.md)

## Proof depends on

- [Even-Shiloach: exact decremental BFS trees in O(mD) total update time](even-shiloach-total-time.md)

## Sources

- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, "Decremental Single-Source Shortest Paths on Undirected Graphs in Near-Linear Total Update Time", FOCS (2014); J. ACM 65(6) (2018), arXiv:1512.08148 (v1 and the journal version), Section 1.
