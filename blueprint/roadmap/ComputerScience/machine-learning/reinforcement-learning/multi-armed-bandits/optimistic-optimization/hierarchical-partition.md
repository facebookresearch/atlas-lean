# Hierarchical partition

Let $\mathcal X$ be a set and $K \ge 1$ an integer. A *hierarchical partition* of $\mathcal X$ with branching factor
$K$ gives, for every depth $h \ge 0$ and every index $i$ with $0 \le i \le K^h - 1$, a set $X_{h,i} \subseteq \mathcal X$,
the *cell* of the *node* $(h, i)$, and a point $x_{h,i} \in X_{h,i}$, the *center* of the cell, such that

- $X_{0,0} = \mathcal X$;
- for every node $(h, i)$, the cells of its $K$ *children* $(h + 1, Ki + k)$, $0 \le k \le K - 1$, are pairwise disjoint
  and their union is $X_{h,i}$.

The node $(0, 0)$ is the *root*, and $(h, i)$ is the *parent* of its children. The nodes form a $K$-ary tree, and,
by induction on $h$, the $K^h$ cells of depth $h$ are pairwise disjoint and cover $\mathcal X$. The algorithms that use
the partition evaluate the function to optimize only at centers of cells.

The sources write the children of $(h, i)$ as $(h + 1, i_1), \dots, (h + 1, i_K)$ without fixing their indices;
the labelling $i_k = Ki + k - 1$ above is one choice, and nothing in this folder depends on it.

For example, the half-open intervals $[i 2^{-h}, (i + 1) 2^{-h})$ with their midpoints form a hierarchical partition
of $[0, 1)$ with $K = 2$.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Section 2.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.2.1 and Figure 3.4.
