# Mirzaian's conjecture: Hamiltonian cycles in segment visibility graphs

Conjecture (A. Mirzaian): for every $m$ and every admissible family of $m$ pairwise disjoint nondegenerate segments in $\mathbb{R}^2$ whose endpoints are not all on one line, the segment visibility graph has a Hamiltonian cycle: there is a permutation $\pi$ of $\{0, \dots, 2m - 1\}$ such that $\pi(t)$ and $\pi(t + 1 \bmod 2m)$ are adjacent in the segment visibility graph for every $t$.

Here $m$ segments in $\mathbb{R}^2$ are given by endpoints $e_0, \dots, e_{2m-1}$, segment $k$ being $s_k = [e_{2k}, e_{2k+1}]$ for $0 \le k < m$; the family is admissible when each $s_k$ is nondegenerate ($e_{2k} \ne e_{2k+1}$) and the closed segments are pairwise disjoint. Two endpoint indices $i \ne j$ are adjacent in the segment visibility graph when $e_i, e_j$ are the two endpoints of the same segment ($\lfloor i/2 \rfloor = \lfloor j/2 \rfloor$) or the open segment $(e_i, e_j)$ is disjoint from every $s_k$. It holds; the resolution is [Segment visibility graphs are Hamiltonian](segment-visibility-hamiltonian-cycle-hol.md).

## Sources

- S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs of points, segments and polygons, arXiv:1012.5187v4, Conjecture 7 (A. Mirzaian), https://arxiv.org/abs/1012.5187v4
