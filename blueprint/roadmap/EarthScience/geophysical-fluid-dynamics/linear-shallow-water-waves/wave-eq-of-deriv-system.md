# Wave equation from the derivative form of the linear system

Let `η(t, x)` and `u(t, x)` be real fields and `H`, `g` real. Write `∂ₓ` for the derivative of
a space slice and `∂ₜ` for that of a time slice, each taken to be `0` where the slice is not
differentiable. Suppose that at every `(t, x)`: the time slice of `η` is differentiable with
`∂ₜη = -H ∂ₓu`; the time slice of `u` is differentiable with `∂ₜu = -g ∂ₓη`; the time slice of
`∂ₓu` is differentiable with derivative `∂ₓ∂ₜu`; and `∂ₓη` is differentiable in `x`. Then
`∂ₜ∂ₜη = g H ∂ₓ∂ₓη` at every `(t, x)`. Because `∂ₓ` is `0` where a slice is not differentiable,
these hypotheses do not require `η` or `u` to be differentiable in `x`, so on their own they
are not the shallow-water equations, which also need those space derivatives.
