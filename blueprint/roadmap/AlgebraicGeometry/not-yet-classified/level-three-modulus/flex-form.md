# Flex form

For a Weierstrass curve $W$ and $x, y$, write $n$ for `W.tangentSlopeNum x y`
and $d$ for `W.deuringA₃ x y`. Then `W.flexForm x y` is $n^2 + a_1nd - (a_2 + 3x)d^2$. When $d$ is
invertible this is $d^2(m^2 + a_1m - a_2 - 3x)$ for $m = n/d$. At a point $(x, y)$ of $W$ over a
field with $d \ne 0$, which is then nonsingular, $m$ is the slope of the tangent line, and the
factor $m^2 + a_1m - a_2 - 3x$ vanishes exactly when the tangent line meets $W$ to order three
there, that is, when $(x, y)$ is a flex. On the curve the flex form is $-\Psi_3(x)$
(`flexForm_eq_neg_eval_Ψ₃`).
