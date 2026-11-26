# Cross covariance of the first-order part and the remainder

Let $\Omega$ be a finite set of scenarios with real weights $p(\omega)$ summing to one, let
$V : \Omega \to \mathbb{R}$ be scenario voltages and let $c_0$, $c_1$, $c_2$ and $v_0$ be real.
Write $E_p X = \sum_{\omega} p(\omega)\,X(\omega)$ and
$\mathrm{Cov}_p(X, Y) = E_p[(X - E_p X)(Y - E_p Y)]$. The [first-order part](quad-linear-part.md)
$L_{v_0}$ and the [remainder](quad-remainder.md) $R_{v_0}(v) = c_2 (v - v_0)^2$ of the
[quadratic calibration](quad-calibration.md) satisfy

$$
\mathrm{Cov}_p\bigl(L_{v_0}(V), R_{v_0}(V)\bigr)
= (c_1 + 2 c_2 v_0)\,c_2\,\mathrm{Cov}_p\bigl(V, (V - v_0)^2\bigr).
$$

It need not vanish: for two scenarios of weight $1/2$ with voltages $v_0$ and $v_0 + 1$,
$\mathrm{Cov}_p(V, (V - v_0)^2) = 1/4$, so the cross covariance is $(c_1 + 2 c_2 v_0)\, c_2 / 4$,
nonzero when $c_2 \ne 0$ and $c_1 + 2 c_2 v_0 \ne 0$. The weights may be signed; when they are also
nonnegative, these are covariances under the probability distribution $p$ on the scenarios.
