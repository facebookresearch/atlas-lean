# Level-three ordinate

For a Weierstrass curve $W$ and points $(x_1, y_1)$, $(x_2, y_2)$,
`W.levelThreeOrdinate x₁ y₁ x₂ y₂` is $(y_2 - y_1 - m(x_2 - x_1))(x_2 - x_1)^3/d^3$, where $m$ is
`W.tangentSlope x₁ y₁` and $d$ is `W.deuringA₃ x₁ y₁`, with the division taken by `Ring.inverse`:
the value is $0$ when $d$ is not a unit. Over a field with $d \ne 0$ and $x_2 \ne x_1$ it is the
ordinate that `W.deuringVariableChange x₁ y₁ u` with $u = d/(x_2 - x_1)$ gives to $(x_2, y_2)$.
