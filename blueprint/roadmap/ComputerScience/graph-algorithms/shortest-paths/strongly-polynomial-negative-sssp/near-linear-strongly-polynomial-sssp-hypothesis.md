# Open problem: near-linear strongly polynomial negative-weight SSSP (hypothesis)

*Hypothesis (open problem).* There is a (possibly randomized, Las Vegas) algorithm in the real RAM that solves the real-weighted SSSP problem, returning either a negative cycle or all distances from $s$, on every directed graph with $n$ vertices and $m$ edges in $m^{1+o(1)}$ time, with no dependence on the edge lengths.

Status: the best proved strongly polynomial bound is $\tilde O(mn^{3/4}+m^{4/5}n)$. For integer lengths at least $-W$, near-linear time $\tilde O(m\log W)$ is achieved, but the factor $\log W$ prevents those algorithms from being strongly polynomial. A weaker open question asks for $\tilde O(mn^{1/2})$ strongly polynomial time, matching the classical scaling bound $O(m\sqrt n\log W)$ without the $\log W$ factor.

## Depends on

- [Real-weighted negative SSSP in the real RAM and strongly polynomial running time](real-weighted-sssp-strongly-polynomial.md)

## Sources

- Yufan Huang, Peter Jin, Kent Quanrud, "Faster negative length shortest paths by bootstrapping hop reducers", SODA (2026), arXiv:2506.00428.
- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
