# Shortest-path closure is a normal form for difference-bound matrices

With the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md), let $m$ be a DBM with $D(m) \ne \emptyset$. Then $G(m)$ has no cycle of strictly negative weight, since adding the constraints $s_{i_{k+1}} - s_{i_k} \le m_{i_k i_{k+1}}$ along a cycle, for any $s \in D(m)$, shows that its weight is at least $0$. Its *closure* $m^*$ has $m^*_{ii} = 0$ and, for $i \ne j$, $m^*_{ij}$ equal to the least weight of a path from $v_i$ to $v_j$ in $G(m)$.

1. **Local characterization.** $m = m^*$ if and only if $m_{ij} \le m_{ik} + m_{kj}$ for all $i, j, k$ and $m_{ii} = 0$ for all $i$.
2. **Saturation.** For all $i, j$ with $m^*_{ij} \ne +\infty$ there is $s \in D(m)$ with $s_j - s_i = m^*_{ij}$.
3. **Normal form.** $m^*$ is the least DBM, for the pointwise order, among those with the same domain as $m$.

The closure is computed in time $O(N^3)$ by the Floyd–Warshall iteration $m_{k+1} = C_k(m_k)$, where $[C_k(n)]_{ii} = 0$ and $[C_k(n)]_{ij} = \min(n_{ij}, n_{ik} + n_{kj})$ for $i \ne j$.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)

## Sources

- A. Miné, "The octagon abstract domain", arXiv:cs/0703084v2, 2007, <https://arxiv.org/abs/cs/0703084>: Section V.B, the definition of the closure $m^*$, Theorem 3 (local definition, saturation and normal form) and the closure algorithm of Figure 7.
