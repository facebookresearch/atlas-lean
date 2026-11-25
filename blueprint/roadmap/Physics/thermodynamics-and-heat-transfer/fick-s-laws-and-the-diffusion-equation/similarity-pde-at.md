# Parabolic rescaling of a solution at one point

Let `D`, `λ`, `x` and `t` be real, `X = λx` and `τ = λ²t`. Suppose `c(X, ·)` has the derivative
`ct(X, τ)` at `τ`; for every real `y`, `c(·, τ)` has the derivative `cx(y, τ)` at `y`; `cx(·, τ)`
has the derivative `cxx(X, τ)` at `X`; and `ct(X, τ) = D cxx(X, τ)`. Then the
[rescaling](scaled-sol.md) `u(x, t) = c(λx, λ²t)` satisfies `∂u/∂t = D ∂²u/∂x²` at `(x, t)`. Only
the time `τ` enters, so this applies to solutions defined only for positive times, such as the
[Gaussian](gauss.md).
