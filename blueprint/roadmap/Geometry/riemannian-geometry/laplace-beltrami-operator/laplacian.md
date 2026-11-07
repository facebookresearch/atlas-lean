# Laplace–Beltrami operator

The Laplace-Beltrami operator applied to `f : M → ℝ` at `x`: `Δf(x)` is the metric
trace `∑ i, hessian I f x (e i) (e i)` over the orthonormal basis
`e = stdOrthonormalBasis ℝ (TangentSpace I x)`, the same basis convention as
`Manifold.scalarCurvature`. For the textbook Hessian, which is bilinear, this trace
does not depend on the orthonormal basis; the regularity caveat of `Manifold.hessian`
applies here unchanged.

Sign convention `Δf = tr_g ∇²f`, the convention `Δ = div ∘ grad` under which `Δ` is the
sum `∑ ∂²/∂x_i²` on Euclidean space and `Δ(‖x‖²) = 2n`; the operator `-Δ` is then the
nonnegative one, and the opposite sign convention is also common. Reference with the
same conventions: Lee, Introduction to Riemannian Manifolds (2nd ed., GTM 176).

Mathlib's flat Laplacian is `Laplacian.laplacian` (instance
`InnerProductSpace.instLaplacian`, notation `Δ` after `open Laplacian`): the trace of
the second derivative over an orthonormal basis of a finite-dimensional real inner
product space. On the model space `𝓘(ℝ, F)`, under
`DifferentiableAt ℝ (fderiv ℝ f) x`, this operator agrees with Mathlib's `Δ`
(same orthonormal-basis trace, same sign); see `laplacian_vectorSpace_eq_laplacian`
for the proved agreement. What is new here is the manifold operator itself.
