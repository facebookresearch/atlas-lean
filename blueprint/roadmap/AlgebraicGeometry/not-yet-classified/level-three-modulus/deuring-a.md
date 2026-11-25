# The $y$-derivative $2y + a_1x + a_3$

For a Weierstrass curve $W$ over a commutative ring
and $x, y$ in that ring, `W.deuringA₃ x y` is $2y + a_1x + a_3$. It is the partial derivative in
$y$ of the Weierstrass polynomial at $(x, y)$ (`deuringA₃_eq_evalEval_polynomialY`), and the
difference $y - y'$, where $y'$ is the ordinate of the negative of $(x, y)$
(`deuringA₃_eq_sub_negY`). Once a flex $(x, y)$ is moved to the origin it is the coefficient $a_3$
of the Deuring form before scaling (`deuringVariableChange_smul`). The quotients of this file
divide by it.
