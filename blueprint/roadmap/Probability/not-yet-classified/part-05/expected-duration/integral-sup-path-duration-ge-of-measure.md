# Expected longest path duration is at least the longest expected path duration

Let $\mu$ be any measure, let each job $j$ have an integrable random duration $D_j$, and let a nonempty finite family of paths each list a multiset of jobs, with path duration $\sum_{j \in p} D_j$. Then

$$\int \max_p \sum_{j \in p} D_j \, d\mu \;\ge\; \max_p \sum_{j \in p} \int D_j \, d\mu.$$

Dependence between jobs is arbitrary.
