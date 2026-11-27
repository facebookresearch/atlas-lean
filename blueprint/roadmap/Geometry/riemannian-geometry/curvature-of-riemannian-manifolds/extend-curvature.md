# Curvature expression of a covariant derivative on extensions

Let $\nabla$ be a covariant
derivative on a vector bundle $V$ over a manifold $M$, let $x \in M$, let $u, v \in T_x M$ and let
$\sigma \in V_x$. Let $X$ and $Y$ be the vector fields on $M$ whose coordinates in the preferred
local trivialization of $TM$ at $x$ are constant, equal to those of $u$ and $v$, on the base set
of that trivialization, with a fixed but unspecified value at each point outside it; let $S$ be
the section of $V$ obtained in the same way from $\sigma$ and the preferred local trivialization
of $V$ at $x$. The curvature expression of $\nabla$ at $x$ on $u$, $v$, $\sigma$ is the vector

$$R(u, v)\sigma = \nabla_u (\nabla_Y S) - \nabla_v (\nabla_X S) - \nabla_{[X, Y](x)} S \in V_x,$$

where $\nabla_Y S$ is the section $y \mapsto \nabla_{Y(y)} S$ and $[X, Y]$ is the Lie bracket.

When $\nabla$ sends $C^2$ sections to $C^1$ sections (for instance the Levi-Civita connection of a
$C^\infty$ metric), this is the curvature tensor
$R(X, Y) = \nabla_X \nabla_Y - \nabla_Y \nabla_X - \nabla_{[X, Y]}$ applied to $u$, $v$, $\sigma$,
and it does not depend on the extensions. For other connections it can depend on values of
$\nabla$ that the axioms of a covariant derivative leave unconstrained.
