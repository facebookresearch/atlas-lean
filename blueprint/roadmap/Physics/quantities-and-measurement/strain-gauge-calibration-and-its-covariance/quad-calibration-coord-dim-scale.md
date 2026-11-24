# Change of units scales the quadratic calibration by the output factor

Let $u_1$ and $u_2$ be two choices of units, each a positive magnitude for every one of the seven
ISQ base quantities. For a dimension $X$ let

$$
s_X = \prod_{q} \left(\frac{u_1(q)}{u_2(q)}\right)^{e_q(X)} > 0
$$

be the factor that converts a coordinate of dimension $X$ from $u_1$ to $u_2$, where $q$ runs over
the base quantities and $e_q(X)$ is the exponent of $X$ at $q$. Let $d$ be an output dimension and
$\mathcal{V}$ the [voltage dimension](voltage-dim.md). For all real $c_0$, $c_1$, $c_2$ and $v$, the
[quadratic calibration](quad-calibration.md) $f(c_0, c_1, c_2; v) = c_0 + c_1 v + c_2 v^2$ satisfies

$$
f\bigl(s_d\,c_0,\ s_{d\mathcal{V}^{-1}}\,c_1,\ s_{d\mathcal{V}^{-2}}\,c_2;\ s_{\mathcal{V}}\,v\bigr)
= s_d\,f(c_0, c_1, c_2; v):
$$

converting the voltage by the voltage factor and each coefficient by the factor of its dimension
converts the output by the output factor. Each term scales by $s_d$, since
$s_{d\mathcal{V}^{-1}} = s_d / s_{\mathcal{V}}$ and
$s_{d\mathcal{V}^{-2}} = s_d / s_{\mathcal{V}}^2$.
