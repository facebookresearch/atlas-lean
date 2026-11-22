# Simple polygon

A polygon in $\mathbb{R}^2$ with vertices $p_0, \dots, p_{n-1}$ (indices
taken mod $n$) and edges the segments $e_i = [p_i, p_{i+1}]$ is simple when consecutive vertices
are distinct ($p_i \ne p_{i+1}$ for all $i$), any two edges $e_i$ and $e_j$ with $i \ne j$,
$j \not\equiv i + 1$ and $i \not\equiv j + 1 \pmod n$ are disjoint, and every two consecutive
edges meet only in their common vertex: $e_i \cap e_{i+1} = \{p_{i+1}\}$ for all $i$.
