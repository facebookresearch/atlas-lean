# Erdős problem 957: product of extreme distance multiplicities

This result proves the proposition stated as [Statement of Erdős problem 957: product of extreme distance multiplicities](extreme-distance-multiplicity-product.md). Precisely, for every $\varepsilon > 0$ there is $N$ such that for every $n \ge N$ and every set $A \subset \mathbb{R}^2$ of exactly $n$ points that determines at least one distance (equivalently $n \ge 2$),

$$f_A(d_1)\, f_A(d_k) \le \left(\tfrac{9}{8} + \varepsilon\right) n^2,$$

where $d_1$ and $d_k$ are the smallest and the largest of the distances $\lVert x - y \rVert$ with $x, y \in A$, $x \ne y$, and $f_A(d)$ is the number of unordered pairs $\{x, y\}$ of distinct points of $A$ with $\lVert x - y \rVert = d$. That is, $f(d_1) f(d_k) \le (9/8 + o(1))\, n^2$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #957. https://www.erdosproblems.com/957
- A. Dumitrescu, A product inequality for extreme distances, Comput. Geom. (2019), 101577; SoCG 2019, LIPIcs 129, Paper 30, Theorem 1. https://drops.dagstuhl.de/storage/00lipics/lipics-vol129-socg2019/LIPIcs.SoCG.2019.30/LIPIcs.SoCG.2019.30.pdf
