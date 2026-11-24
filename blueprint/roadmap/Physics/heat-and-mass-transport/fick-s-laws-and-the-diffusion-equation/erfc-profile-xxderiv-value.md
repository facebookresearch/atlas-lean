# Second spatial derivative of the error-function profile for D, t > 0

Let `D > 0` and `t > 0`. For all real `cs` and `x`, the map `x ↦ ∂C/∂x(x, t)` of the
[error-function profile](erfc-profile.md) `C(x, t) = cs · erfc(x/√(4Dt))` has the derivative

`∂²C/∂x²(x, t) = cs · erfc″(x/√(4Dt)) / (√(4Dt))²`,

with [`erfc″(y) = (4y/√π) exp(-y²)`](erfc-deriv2.md).
