# Frobenius determinant theorem

Let $G$ be a finite group and let $r$ be the number of
conjugacy classes of $G$. Then there exist polynomials $p_1, \dots, p_r$ in
$\mathbb{C}[x_g : g \in G]$ such that each $p_j$ is irreducible, $p_i$ and $p_j$ are not associated
for $i \neq j$, and the group determinant of $G$ equals $\prod_{j=1}^{r} p_j^{\deg p_j}$, where
$\deg p_j$ is the total degree of $p_j$.

## Sources

- Knill, *Some fundamental theorems in mathematics*, §171. Problem `frobenius_group_determinant` of the lean-eval benchmark.
