# Jacobian matrix of the Hodgkin–Huxley vector field

For a [parameter set](params.md) and a state $x = (V, m, h, n)$, the Jacobian matrix of the
[vector field](field.md) is

$$J(x) = \begin{pmatrix}
-\dfrac{g_{Na} m^3 h + g_K n^4 + g_L}{C} & -\dfrac{3 g_{Na} m^2 h\,(V - E_{Na})}{C}
  & -\dfrac{g_{Na} m^3 (V - E_{Na})}{C} & -\dfrac{4 g_K n^3 (V - E_K)}{C} \\
a_m & -(\alpha_m + \beta_m) & 0 & 0 \\
a_h & 0 & -(\alpha_h + \beta_h) & 0 \\
a_n & 0 & 0 & -(\alpha_n + \beta_n)
\end{pmatrix},$$

where the rates are evaluated at $V$, $a_y = \alpha_y'(V)(1 - y) - \beta_y'(V)\,y$ for
$y = m, h, n$, and a prime denotes the derivative, taken as $0$ at a point where it does not exist.
With the convention $x/0 = 0$, the first row is $0$ when $C = 0$. The matrix is the derivative of
the vector field at $x$ for every parameter set ([linearization](has-fderiv-at-field.md)).
