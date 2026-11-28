# Variable change to Deuring form

For a Weierstrass curve $W$, a point $(x_1, y_1)$ and a
unit $u$, `W.deuringVariableChange x₁ y₁ u` is the variable change
$(u, r, s, t) = (u, x_1, m, y_1)$, where $m$ is `W.tangentSlope x₁ y₁`; in coordinates,
$x = u^2x' + x_1$ and $y = u^3y' + u^2mx' + y_1$. It moves $(x_1, y_1)$ to the origin. When
$(x_1, y_1)$ is a point of $W$ at which $2y_1 + a_1x_1 + a_3$ is a unit, it also moves the tangent
line there to $y' = 0$; over a field, at such a point where the flex form vanishes, it gives the
Deuring form (`deuringVariableChange_smul`).
