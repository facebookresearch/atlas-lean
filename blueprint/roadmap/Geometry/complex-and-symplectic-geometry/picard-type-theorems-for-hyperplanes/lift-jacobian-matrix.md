# Homogeneous Jacobian matrix of a map $\mathbb{C}^n \to \mathbb{C}^{n+1}$

For a map $F : \mathbb{C}^n \to \mathbb{C}^{n+1}$ and a point $z \in \mathbb{C}^n$, this is the $(n+1) \times (n+1)$ complex matrix whose columns are

$$F(z),\ \partial_1 F(z),\ \dots,\ \partial_n F(z),$$

where $\partial_j F(z) = DF(z)\, e_j$ is the complex derivative of $F$ at $z$ applied to the $j$-th standard basis vector (taken to be $0$ if $F$ is not complex differentiable at $z$).

When $F$ is a holomorphic lift in homogeneous coordinates of a map $f : \mathbb{C}^n \to \mathbb{P}^n(\mathbb{C})$ with $F(z) \ne 0$, the determinant of this matrix is nonzero exactly when the Jacobian of $f$ has rank $n$ at $z$: in an affine chart where $F_0(z) \ne 0$ it equals $F_0(z)^{n+1}$ times the Jacobian determinant of $f$.
