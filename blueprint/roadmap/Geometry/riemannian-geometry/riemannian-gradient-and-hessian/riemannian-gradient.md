# Riemannian gradient

Let $M$ be a $C^1$ manifold modelled on a complete real normed
space, with a Riemannian metric, and let $f : M \to \mathbb{R}$ and $x \in M$. The Riemannian
gradient $\operatorname{grad} f(x) = (df_x)^\sharp \in T_xM$ is the image of the differential
$df_x$ of $f$ at $x$ under the inverse of the Riesz isomorphism
$T_xM \to (T_xM)^*$, $w \mapsto \langle w, \cdot \rangle$, given by the metric at $x$. It is the
unique tangent vector with $\langle \operatorname{grad} f(x), v \rangle = df_x(v)$ for all
$v \in T_xM$.
