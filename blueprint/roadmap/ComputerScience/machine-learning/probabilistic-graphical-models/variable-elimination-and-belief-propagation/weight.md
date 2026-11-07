# Weight of an assignment in a tree model

Let $\alpha$ be a type and let $m$ be a pairwise
model on a tree with vertices $0, \dots, n$, with unary factors $\varphi_i : \alpha \to \mathbb{R}$
for each vertex $i$, and with factor $\psi_k : \alpha \times \alpha \to \mathbb{R}$ on the edge
between vertex $k + 1$ and its parent $p(k + 1)$ for each $k < n$. The unnormalized weight of an
assignment $x : \{0, \dots, n\} \to \alpha$ is the real number

$$w(x) = \prod_{i=0}^{n} \varphi_i(x_i) \cdot \prod_{k=0}^{n-1} \psi_k(x_{k+1}, x_{p(k+1)}),$$

the product of all factors evaluated at $x$.
