# The $y$-derivative $2y + a_1x + a_3$

For a Weierstrass curve $W$ over a commutative ring
and $x, y$ in that ring, `W.deuringA₃ x y` is $2y + a_1x + a_3$. It is the partial derivative in
$y$ of the Weierstrass polynomial at $(x, y)$ (`deuringA₃_eq_evalEval_polynomialY`), and the
difference $y - y'$ for $y'$ = `W.toAffine.negY x y`, which is the ordinate of $-(x, y)$ when
$(x, y)$ is a nonsingular point of $W$ (`deuringA₃_eq_sub_negY`). At a point $(x, y)$ of $W$ over
a field where it is nonzero and the flex form vanishes, it is the coefficient $a_3$ of the Deuring
form before scaling (`deuringVariableChange_smul`). The quotients of this file divide by it.
