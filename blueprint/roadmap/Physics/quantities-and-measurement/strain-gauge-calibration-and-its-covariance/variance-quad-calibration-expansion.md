# Output variance splits into linear, remainder and cross terms

Let $\Omega$ be a finite set of scenarios with arbitrary real weights $p(\omega)$, let
$V : \Omega \to \mathbb{R}$ be scenario voltages and let $c_0$, $c_1$, $c_2$ and $v_0$ be real.
Write $E_p X = \sum_{\omega} p(\omega)\,X(\omega)$,
$\mathrm{Cov}_p(X, Y) = E_p[(X - E_p X)(Y - E_p Y)]$ and $\mathrm{Var}_p X = \mathrm{Cov}_p(X, X)$.
With $f$ the [quadratic calibration](quad-calibration.md), $L_{v_0}$ its
[first-order part](quad-linear-part.md) and $R_{v_0}$ its [remainder](quad-remainder.md) at $v_0$,

$$
\mathrm{Var}_p f(V) = \mathrm{Var}_p L_{v_0}(V) + \mathrm{Var}_p R_{v_0}(V) +
2\,\mathrm{Cov}_p\bigl(L_{v_0}(V), R_{v_0}(V)\bigr).
$$

The identity holds for all real weights, signed or not, of any total. For nonnegative weights
summing to one it splits the variance of the calibrated output under the probability distribution
$p$, keeping the variance of the remainder and the cross term.
