# Variable change towards Legendre form

For a Weierstrass curve $W$ over a field, $x_1$
and $w \ne 0$, `W.legendreVariableChange x₁ w hw` is the variable change
$(u, r, s, t) = (w, x_1, -a_1/2, -(a_3 + x_1a_1)/2)$, that is, $x = w^2x' + x_1$ and
$y = w^3y' - (a_1/2)w^2x' - (a_3 + x_1a_1)/2$. When $2 \ne 0$ it completes the square, so the new
curve has $a_1 = a_3 = 0$, and it moves $x = x_1$ to $x' = 0$.
