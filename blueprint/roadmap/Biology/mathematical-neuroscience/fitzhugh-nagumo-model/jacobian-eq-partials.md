# The Jacobian entries are the partial derivatives of the field

For all real `a`, `b`, `ε`, `I`, `v` and `w`, the entries of the [Jacobian](jacobian.md) `J` at
voltage `v` are the partial derivatives of the [field](field.md) at `(v, w)`: the voltage component
`u - u³/3 - x + I` has `∂/∂u = 1 - v² = J₁₁` and `∂/∂x = -1 = J₁₂`, and the recovery component
`ε (u + a - b x)` has `∂/∂u = ε = J₂₁` and `∂/∂x = -ε b = J₂₂`, all at `(u, x) = (v, w)`.
