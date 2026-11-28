# Real-weighted negative SSSP in the real RAM and strongly polynomial running time

Let $G=(V,E,\ell)$ be a directed graph with $n$ vertices, $m\ge n$ edges and real edge lengths $\ell:E\to\mathbb{R}$, and let $s\in V$. The *real-weighted SSSP problem* asks for either a cycle of negative length or, when there is none, the distances $d(s,v)=\inf\{\ell(P): P \text{ an } s\text{-}v \text{ walk}\}$ for all $v$ (with $d(s,v)=\infty$ for $v$ not reachable from $s$), equivalently a shortest-path tree spanning the vertices reachable from $s$. The model of computation is the real RAM: lengths are stored exactly and addition, subtraction and comparison of reals cost $O(1)$, with word-RAM operations on indices. An algorithm is *strongly polynomial* if its number of operations is bounded by a polynomial in $n$ and $m$ alone, independent of the magnitudes of the lengths. The Bellman-Ford-Moore-Shimbel algorithm solves the problem in $O(mn)$ time, and no asymptotically faster strongly polynomial algorithm was known before 2024. By splitting high-degree vertices one may assume maximum in- and out-degree $O(m/n)$ without changing $n$ and $m$ by more than constant factors.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
- Richard Bellman, "On a Routing Problem", Quarterly of Applied Mathematics 16(1) (1958).
- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
