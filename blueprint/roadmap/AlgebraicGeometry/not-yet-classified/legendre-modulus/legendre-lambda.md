# Legendre parameter

For a Weierstrass curve $W$ over a field and $x_1, x_2$ in it,
`W.legendreLambda x₁ x₂` is $(x_3 - x_1)/(x_2 - x_1)$, where $x_3$ is `W.thirdTwoTorsionX x₁ x₂`;
division by zero gives $0$, so the value is $0$ when $x_2 = x_1$. For the Legendre curve
$y^2 = x(x - 1)(x - t)$ with $x_1 = 0$ and $x_2 = 1$ it is $t$ when $2 \ne 0$
(`legendreLambda_legendreCurve`).
