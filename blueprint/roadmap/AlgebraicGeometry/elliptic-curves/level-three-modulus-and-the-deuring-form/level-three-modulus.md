# Level-three modulus

For a Weierstrass curve $W$, a point $(x_1, y_1)$ and an abscissa
$x_2$, `W.levelThreeModulus x₁ y₁ x₂` is $a(x_2 - x_1)/d$, where $a$ is `W.deuringA₁ x₁ y₁` and $d$
is `W.deuringA₃ x₁ y₁`, with the division taken by `Ring.inverse`: the value is $0$ when $d$ is not
a unit. When $(x_1, y_1)$ is a point of $W$ over a field at which $d \ne 0$ and the flex form
vanishes, and $x_2 \ne x_1$, it is the coefficient $\alpha$ of the Deuring form
$y^2 + \alpha xy + \beta y = x^3$ reached with the scaling $u = d/(x_2 - x_1)$
(`deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus`).
