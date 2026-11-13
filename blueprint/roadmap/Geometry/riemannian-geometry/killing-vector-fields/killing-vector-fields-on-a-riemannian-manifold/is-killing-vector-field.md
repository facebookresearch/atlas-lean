# Killing vector field

Let $M$ be a finite-dimensional smooth manifold, possibly with
boundary or corners, with a smooth Riemannian metric $g = \langle \cdot, \cdot \rangle$ and its
Levi-Civita connection $\nabla$. A vector field $X$ on $M$ is a Killing vector field if $X$ is
smooth and satisfies Killing's equation: for every point $x \in M$ and all tangent vectors
$u, v \in T_x M$,

$$\langle \nabla_u X, v \rangle + \langle u, \nabla_v X \rangle = 0.$$

In index notation this is $\nabla_i X_j + \nabla_j X_i = 0$, and it is equivalent to the
vanishing of the Lie derivative $L_X g$ of the metric. Smoothness is part of the definition, as
in the textbook definition.

## Sources

- Burns and Matveev (2021), §10.2, for motivation: a Killing field $V$ gives the linear first integral $\xi \mapsto g(V, \xi)$ of geodesic flow.
