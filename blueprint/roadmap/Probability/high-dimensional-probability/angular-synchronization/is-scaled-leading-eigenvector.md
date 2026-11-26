# Leading eigenvectors scaled to norm $\sqrt{n}$

For a matrix $C \in \mathbb{C}^{n \times n}$, a vector $x_0 \in \mathbb{C}^n$ is a scaled leading eigenvector of $C$ if $\lVert x_0 \rVert_2^2 = \sum_k \lvert (x_0)_k \rvert^2 = n$ and

$$\operatorname{Re}(y^* C y) \le \operatorname{Re}(x_0^* C x_0) \quad \text{for every } y \in \mathbb{C}^n \text{ with } \lVert y \rVert_2^2 = n.$$

When $C$ is Hermitian and $n > 0$, $y^* C y$ is real and these are exactly the eigenvectors of $C$ for its largest eigenvalue, scaled to norm $\sqrt{n}$. For $n = 0$ the definition still applies: the empty vector satisfies both conditions, but it is the zero vector and there is no eigenvalue, so the spectral reading does not apply.
