# Hoffmann-Tóth: disjoint segments admit a Hamiltonian polygon

This result proves the proposition stated as [Mirzaian's conjecture: Hamiltonian polygons of disjoint segments](segment-visibility-hamiltonian-polygon.md). Precisely, for every $m$ and every admissible family of $m$ pairwise disjoint nondegenerate segments in $\mathbb{R}^2$ whose endpoints are not all on one line, there is a permutation $\pi$ of $\{0, \dots, 2m - 1\}$ such that $\pi(t)$ and $\pi(t + 1 \bmod 2m)$ are adjacent in the segment visibility graph for every $t$, and moreover $e_{\pi(0)}, e_{\pi(1)}, \dots, e_{\pi(2m-1)}$ is a simple polygon.

Here $m$ segments in $\mathbb{R}^2$ are given by endpoints $e_0, \dots, e_{2m-1}$, segment $k$ being $s_k = [e_{2k}, e_{2k+1}]$ for $0 \le k < m$; the family is admissible when each $s_k$ is nondegenerate ($e_{2k} \ne e_{2k+1}$) and the closed segments are pairwise disjoint. Two endpoint indices $i \ne j$ are adjacent in the segment visibility graph when $e_i, e_j$ are the two endpoints of the same segment ($\lfloor i/2 \rfloor = \lfloor j/2 \rfloor$) or the open segment $(e_i, e_j)$ is disjoint from every $s_k$. A sequence $v_0, \dots, v_{n-1}$ is a simple polygon when $n \ge 3$, $v_i \ne v_{i+1}$ for all $i$, consecutive edges $[v_i, v_{i+1}]$ and $[v_{i+1}, v_{i+2}]$ meet exactly in $\{v_{i+1}\}$, and non-consecutive edges are disjoint (indices mod $n$).

## Sources

- S. K. Ghosh and P. P. Goswami, Unsolved problems in visibility graphs of points, segments and polygons, arXiv:1012.5187v4, Conjecture 8 (A. Mirzaian), https://arxiv.org/abs/1012.5187v4
- M. Hoffmann and Cs. D. Tóth, Segment endpoint visibility graphs are Hamiltonian, Comput. Geom. 26 (2003), 47-68, https://doi.org/10.1016/S0925-7721(02)00172-4
