# Level-three abscissa

For a Weierstrass curve $W$, a point $(x_1, y_1)$ and an abscissa
$x_2$, `W.levelThreeAbscissa x₁ y₁ x₂` is $(x_2 - x_1)^3/d^2$, where $d$ is `W.deuringA₃ x₁ y₁`,
with the division taken by `Ring.inverse`: the value is $0$ when $d$ is not a unit. Over a field
with $d \ne 0$ and $x_2 \ne x_1$ it is the abscissa that the scaling $u = d/(x_2 - x_1)$ of
`levelThreeModulus` gives to $x_2$. When moreover $(x_1, y_1)$ is a point of $W$ at which the flex
form vanishes, it is the coefficient $\beta$ of the Deuring form
(`deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus`).
