# Local solutions of the incompressible Euler equations

Let $T \in \mathbb{R}$, let
$u_0 : \mathbb{R}^3 \to \mathbb{R}^3$, and let $p : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}$
and $u : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}^3$. Write $\partial_t u$ for the time
derivative of $u$, $(u \cdot \nabla_x) u$ for the spatial directional derivative of $u$ in the
direction of $u$, and $\nabla_x p$ for the spatial gradient of $p$. Then $u$ is a local solution
of the incompressible Euler equations up to time $T$, with pressure $p$ and initial data $u_0$,
if $u$ and $p$ are continuously differentiable, as functions of $(x, t)$, on
$\mathbb{R}^3 \times [0, T)$, if for all $x \in \mathbb{R}^3$ and $t \in (0, T)$

$$\partial_t u(x, t) + (u \cdot \nabla_x) u(x, t) + \nabla_x p(x, t) = 0,$$

if for every $t \in (0, T)$ the divergence of $u(\cdot, t)$ is $0$ at every point of
$\mathbb{R}^3$, and if $u(\cdot, 0) = u_0$.
