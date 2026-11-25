# Laplace–Beltrami operator

Let $M$ be a smooth manifold modelled on a finite-dimensional real normed space, with a smooth Riemannian metric. The
Laplace–Beltrami operator applied to $f : M \to \mathbb{R}$ at $x$ is the metric trace
$\Delta f(x) = \sum_i \nabla^2 f(e_i, e_i)$ of the
[covariant Hessian](../riemannian-gradient-and-hessian/hessian.md) over a fixed orthonormal basis $(e_i)$ of $T_xM$,
the same basis convention as for the scalar curvature. For the textbook Hessian, which is bilinear, this trace does
not depend on the orthonormal basis.

Sign convention $\Delta f = \operatorname{tr}_g \nabla^2 f$, the convention $\Delta = \operatorname{div} \circ \operatorname{grad}$
under which $\Delta$ is the sum $\sum_i \partial^2/\partial x_i^2$ on Euclidean space and $\Delta(\|x\|^2) = 2n$; the
operator $-\Delta$ is then the nonnegative one, and the opposite sign convention is also common. Reference with the
same conventions: Lee, Introduction to Riemannian Manifolds (2nd ed., GTM 176).

On a finite-dimensional real inner product space with its standard metric, this operator agrees with the flat
Laplacian, the trace of the second derivative over an orthonormal basis (same sign), at every point where the
derivative of $f$ is differentiable: see
[the Laplacian on a vector space](laplacian-vector-space-eq-laplacian.md).
