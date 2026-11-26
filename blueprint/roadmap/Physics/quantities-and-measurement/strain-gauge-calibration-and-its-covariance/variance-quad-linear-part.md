# Variance of the first-order part, for weights summing to one

Let $\Omega$ be a finite set of scenarios with real weights $p(\omega)$ summing to one, let
$V : \Omega \to \mathbb{R}$ be scenario voltages and let $c_0$, $c_1$, $c_2$ and $v_0$ be real.
Write $E_p X = \sum_{\omega} p(\omega)\,X(\omega)$ and $\mathrm{Var}_p X = E_p[(X - E_p X)^2]$. The
[first-order part](quad-linear-part.md) $L_{v_0}(v) = f(v_0) + (c_1 + 2 c_2 v_0)(v - v_0)$ of the
[quadratic calibration](quad-calibration.md) $f$ is affine in $v$, and

$$
\mathrm{Var}_p L_{v_0}(V) = (c_1 + 2 c_2 v_0)^2\,\mathrm{Var}_p V,
$$

where $c_1 + 2 c_2 v_0 = f'(v_0)$ is its slope. The weights may be signed; when they are also
nonnegative, these are variances under the probability distribution $p$ on the scenarios.
