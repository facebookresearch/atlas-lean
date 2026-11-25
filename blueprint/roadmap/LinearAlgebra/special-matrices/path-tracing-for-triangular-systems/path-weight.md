# Weight of a path for a coefficient matrix

For $n \in \mathbb{N}$, a monoid $R$ and a matrix $B$ over $R$ indexed by $\{0, \dots, n-1\}$, the weight of a list of nodes $p = [v_0, v_1, \dots, v_k]$ is $w_B(p) = B_{v_1 v_0} B_{v_2 v_1} \cdots B_{v_k v_{k-1}}$ (a one-node or empty list has weight $1$). Reading $B_{uv}$ as the coefficient of the edge $v \to u$, it is the product of the edge coefficients along the path $v_0 \to v_1 \to \cdots \to v_k$.
