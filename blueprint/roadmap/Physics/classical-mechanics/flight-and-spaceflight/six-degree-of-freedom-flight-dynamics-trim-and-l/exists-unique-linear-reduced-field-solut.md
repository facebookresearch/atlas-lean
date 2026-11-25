# The reduced linear plant has a unique global solution

For every initial state `e₀ ∈ ℝ⁴` there is exactly one function `e` from the reals to `ℝ⁴` with
`e(0) = e₀` and `e'(t) = A e(t)` at every real time `t`, where `A e` is the
[reduced linear plant](linear-reduced-field.md). The field is linear, hence globally Lipschitz,
and [global existence for globally Lipschitz fields](../../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md)
applies.
