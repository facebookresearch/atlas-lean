# Deuring normal form

For $\alpha, \beta$ in a commutative ring $R$, `deuringCurve α β` is
the Weierstrass curve $y^2 + \alpha xy + \beta y = x^3$, with discriminant
$\beta^3(\alpha^3 - 27\beta)$ (`deuringCurve_Δ`). Over a field with $\beta \ne 0$, the origin is
a nonsingular point of the curve, and its tangent line $y = 0$ meets the curve only there, to
order three, so the origin is a flex; when the curve is moreover elliptic, the origin is a point of
order three. Conversely, over a field `deuringVariableChange_smul` puts a Weierstrass curve in this
form, with a given point at the origin, when that point lies on the curve, satisfies
$2y + a_1x + a_3 \ne 0$ and has vanishing flex form, that is, when it is a flex whose tangent line
is not vertical.
