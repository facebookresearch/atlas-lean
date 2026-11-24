# Lift Coefficient

Lift coefficient for a two-dimensional force per unit span:
`L / (ρ * U^2 * c / 2)`, where `L` is signed lift and `c` is chord.
As usual in Lean, division by zero is totalized; the coefficient
formulas below assume the factors being cancelled are nonzero.
