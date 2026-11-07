# Solutions of the $N$-body problem

Let $E$ be a finite-dimensional real inner product
space, let $N$ be a natural number, give $E^N$ the inner product
$\langle u, v \rangle = \sum_i \langle u_i, v_i \rangle$, and let
$m = (m_1, \dots, m_N) \in \mathbb{R}^N$ be masses. Let
$U(y) = \sum_{i < j} m_i m_j \lVert y_i - y_j \rVert^{-1}$ be the Newtonian potential on $E^N$,
and for $f : E^N \to \mathbb{R}$ let $\nabla_m f(y) \in E^N$ be the mass-weighted gradient, with
components $(\nabla_m f(y))_i = m_i^{-1} (\nabla f(y))_i$, where $\nabla f$ is the gradient of $f$.
A curve $x : \mathbb{R} \to E^N$ is a solution of the $N$-body problem with masses $m$ if $x$ is
$C^2$ on $(0, \infty)$, $x$ is continuous at $0$, and $x''(t) = \nabla_m U(x(t))$ for every
$t > 0$.

In the formalization $0^{-1} = 0$, so a collision term contributes $0$ to $U$ and a zero mass
gives a zero component of $\nabla_m f$. Moreover $\nabla f(y) = 0$ at every point $y$ where $f$
is not differentiable; for instance, a curve that stays at a collision with $x'' = 0$ can be a
solution in this sense.
