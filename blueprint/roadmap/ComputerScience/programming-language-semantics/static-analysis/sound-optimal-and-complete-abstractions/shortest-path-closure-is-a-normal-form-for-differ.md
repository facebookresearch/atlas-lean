# Shortest-path closure is a normal form for difference-bound matrices

With the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md), let $m$ be a DBM with $D(m) \ne \emptyset$. Then $G(m)$ has no cycle of strictly negative weight, since adding the constraints $s_{i_{k+1}} - s_{i_k} \le m_{i_k i_{k+1}}$ along a cycle, for any $s \in D(m)$, shows that its weight is at least $0$. Its *closure* $m^*$ has $m^*_{ii} = 0$ and, for $i \ne j$, $m^*_{ij}$ equal to the least weight of a path from $v_i$ to $v_j$ in $G(m)$ if such a path exists, and $+\infty$ otherwise.

1. **Local characterization.** $m = m^*$ if and only if $m_{ij} \le m_{ik} + m_{kj}$ for all $i, j, k$ and $m_{ii} = 0$ for all $i$.
2. **Saturation.** For all $i, j$ with $m^*_{ij} \ne +\infty$ there is $s \in D(m)$ with $s_j - s_i = m^*_{ij}$.
3. **Normal form.** $m^*$ is the least DBM, for the pointwise order, among those with the same domain as $m$.

For integer bounds, the closure is computed by the Floyd–Warshall iteration $m_{k+1} = C_k(m_k)$, where $[C_k(n)]_{ii} = 0$ and $[C_k(n)]_{ij} = \min(n_{ij}, n_{ik} + n_{kj})$ for $i \ne j$: the [Floyd–Warshall theorem](../../../graph-algorithms/shortest-paths/floyd-warshall-algorithm/floyd-warshall-distance-spec.md) gives the least path weights and the iteration [takes $N^2 + N^3$ steps](../../../graph-algorithms/shortest-paths/floyd-warshall-algorithm/floyd-warshall-time.md). Rational bounds reduce to this case: multiplying all finite entries by a common positive denominator multiplies every path weight by the same positive factor. The real case is not claimed here.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)

## Proof depends on

- [Floyd–Warshall computes shortest-path distances](../../../graph-algorithms/shortest-paths/floyd-warshall-algorithm/floyd-warshall-distance-spec.md)
- [Floyd–Warshall performs $n^2 + n^3$ steps](../../../graph-algorithms/shortest-paths/floyd-warshall-algorithm/floyd-warshall-time.md)

## Sources

- A. Miné, "The octagon abstract domain", *Proceedings of the Eighth Working Conference on Reverse Engineering (WCRE 2001)*, IEEE, 2001, pp. 310–319, doi:10.1109/WCRE.2001.957836, author copy <https://arxiv.org/abs/cs/0703084>: Section V.B, the definition of the closure $m^*$, Theorem 3 (local definition, saturation and normal form) and the closure algorithm of Figure 7.
