# Covariant Hessian

Let $M$ be a smooth manifold modelled on a finite-dimensional real
normed space, with a smooth Riemannian metric and its Levi-Civita connection $\nabla$. For
$f : M \to \mathbb{R}$, a point $x \in M$ and tangent vectors $u, v \in T_xM$, let $V$ be the
extension of $v$ to a vector field with constant coordinates in the preferred chart at $x$, so
that $V(x) = v$. The Hessian of $f$ at $x$ is the real number

$$\nabla^2 f(u, v) = d\big(y \mapsto df_y(V(y))\big)_x(u) - df_x(\nabla_u V),$$

that is, $u(Vf) - df_x(\nabla_u V)$, where $df_y$ is the differential of $f$ at $y$.

This is the textbook Hessian $\nabla^2 f = \nabla(df)$, $\nabla^2 f(u, v) = (\nabla_u df)(v)$
(Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, Ch. 4), taken as a function of two tangent vectors.
