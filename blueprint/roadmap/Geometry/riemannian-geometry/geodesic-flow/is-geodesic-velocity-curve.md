# Geodesic velocity curves

Let $M$ be a $C^2$ manifold (boundary and corners allowed)
modeled on a finite-dimensional real space, with a $C^1$ Riemannian metric
$\langle \cdot, \cdot \rangle$ and Levi-Civita connection $\nabla$. A curve
$u : \mathbb{R} \to TM$, with base curve $\gamma$ ($\gamma(t)$ is the base point of $u(t)$), is a
geodesic velocity curve when for every $t \in \mathbb{R}$: $\gamma$ is differentiable at $t$ with
velocity $\gamma'(t) = u(t)$; and for every vector field $W$ on $M$ that is differentiable at
$\gamma(t)$, the function $s \mapsto \langle u(s), W(\gamma(s)) \rangle$ has derivative
$\langle u(t), \nabla_{u(t)} W \rangle$ at $t$.

The second condition is the weak form of the geodesic equation $\nabla_{\gamma'} \gamma' = 0$:
by metric compatibility, $\frac{d}{dt} \langle \gamma', W \circ \gamma \rangle =
\langle \nabla_{\gamma'} \gamma', W \rangle + \langle \gamma', \nabla_{\gamma'} W \rangle$, and the
values $W(\gamma(t))$ exhaust the tangent space. The two conditions force $\gamma$ to be $C^2$ in
charts, where the weak form is equivalent to $\nabla_{\gamma'} \gamma' = 0$; no further
smoothness of the curve is assumed.
