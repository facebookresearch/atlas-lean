# Conditional decay at a branch point with a Hurwitz Jacobian

Let `V` be real, and suppose the [Jacobian](../hodgkin-huxley-model/jac.md) of the squid
Hodgkin–Huxley field at the [branch point](eq-point.md) `x* = (V, m∞(V), h∞(V), n∞(V))` is
[Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md):
every complex eigenvalue has negative real part. The applied current enters the vector field only as
a constant term of its voltage component, so this Jacobian is the same for every applied current.
Take the [squid system with applied current](squid-i.md) `I = I∞(V)`, the
[squid steady-state current](iss.md) at `V`, of which `x*` is an equilibrium. Then there are
`δ, K, α > 0` such that every [solution](../hodgkin-huxley-model/is-solution.md) `x` on `[0, ∞)`
(differentiable at every `t ≥ 0`, with derivative the field at `x(t)`) with `‖x(0) - x*‖ < δ`
satisfies `‖x(t) - x*‖ ≤ K e^{-α t} ‖x(0) - x*‖` for every `t ≥ 0`, in the maximum norm on `ℝ⁴`.

This specializes the
[conditional decay form of Lyapunov's indirect method](../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md):
it does not assert that such solutions exist, so it is not by itself local exponential stability.
