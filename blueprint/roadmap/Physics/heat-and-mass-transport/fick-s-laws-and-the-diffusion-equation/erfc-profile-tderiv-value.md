# Time derivative of the error-function profile for D, t > 0

Let `D > 0` and `t > 0`. For all real `cs` and `x`, the [error-function profile](erfc-profile.md)
`C(x, t) = cs · erfc(x/√(4Dt))` has, as a function of `t`, the derivative given by the chain rule
through `ξ = x/√(4Dt)`:

`∂C/∂t(x, t) = cs · erfc′(ξ) · (-x · 4D/(2√(4Dt))) / (√(4Dt))² = -cs x erfc′(ξ) / (2t √(4Dt))`,

with [`erfc′(y) = -(2/√π) exp(-y²)`](erfc-deriv.md).
