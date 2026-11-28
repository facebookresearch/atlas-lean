# Is Tangent Line

The line `c(X - x₀) + d(Y - y₀) = 0`, with `(c, d) ≠ 0` and coefficients in `F`, is a
*tangent line* at the double point `(x₀, y₀)`: `(x₀, y₀)` is a double point
(`WeierstrassCurve.IsDoublePoint`), and the linear form `c(X - x₀) + d(Y - y₀)` divides the
degree-two part `f₂` (Milne, *Elliptic Curves*, Chapter I, §1, p. 8: at a singular point of
multiplicity `m`, the tangent lines are the lines `Lᵢ = 0` for the linear factors `Lᵢ` of `f_m`
over an algebraic closure, here `m = 2`). Over a field that is not algebraically closed, this
captures only the tangent lines defined over `F`. A line is recorded by its coefficient vector
`(c, d)`, which is determined by the line up to a nonzero scalar; accordingly, in `IsNode` and
`IsCusp` two tangent lines `(c, d)` and `(c', d')` are distinct when `c * d' - d * c' ≠ 0`.
