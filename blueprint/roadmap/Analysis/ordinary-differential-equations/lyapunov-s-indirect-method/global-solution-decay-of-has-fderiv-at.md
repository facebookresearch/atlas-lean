# Lyapunov's indirect method (linearized stability), conditional decay form

Let
`f (x⋆) = 0` and let `f` be differentiable at `x⋆` with Jacobian matrix `A`. If `A` is Hurwitz,
then for some `δ, C, α > 0`, every solution of `x' = f(x)` on `[0, ∞)` with
`‖x(0) - x⋆‖ < δ` satisfies `‖x(t) - x⋆‖ ≤ C e^{-α t} ‖x(0) - x⋆‖` for all `t ≥ 0`.
This is conditional on the solution being defined on all of `[0, ∞)`; it does not assert
solution existence, so it is not by itself local exponential stability (Khalil 2002,
Theorem 4.7, which assumes `f` is `C¹` and concludes asymptotic stability).
