# Infected-block Jacobian F − V at the disease-free equilibrium

Let `N ≠ 0`, and let `β`, `σ`, `γ`, the time `t` and the removed level `r` be any real numbers.
The components along `E` and `I` of the [SEIR vector field](seir-field.md) at the state
`(N, E, I, r)`, as functions of `(E, I)`, have at `E = I = 0` the derivative with matrix

`F - V = [[0, β], [0, 0]] - [[σ, 0], [-σ, γ]] = [[-σ, β], [σ, -γ]]`

(rows listed in order), the difference of the
[new-infection Jacobian](has-fderiv-at-new-infections.md) and the
[transfer Jacobian](has-fderiv-at-transfers.md).
