# The coefficient $a_1 + 2m$

For a Weierstrass curve $W$ and $x, y$, `W.deuringA₁ x y` is
$a_1 + 2m$, where $m$ is `W.tangentSlope x y`. Once a flex $(x, y)$ is moved to the origin it is
the coefficient $a_1$ of the Deuring form before scaling (`deuringVariableChange_smul`). Because
`tangentSlope` is totalized, the value is $a_1$ when $2y + a_1x + a_3$ is not a unit.
