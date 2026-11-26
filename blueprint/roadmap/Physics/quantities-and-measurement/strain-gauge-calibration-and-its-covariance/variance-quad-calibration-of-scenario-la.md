# Output variance of the quadratic calibration under a scenario law

Let $\Omega$ be a finite set of scenarios and let $(p, V)$ be a [scenario law](scenario-law-in.md)
in $[a, b]$: weights $p(\omega) \ge 0$ summing to one and scenario voltages $a \le V(\omega) \le b$.
Let $v_0 \in [a, b]$ be a base voltage and $c_0$, $c_1$, $c_2$ real, and write
$E_p X = \sum_{\omega} p(\omega)\,X(\omega)$, $\mathrm{Cov}_p(X, Y) = E_p[(X - E_p X)(Y - E_p Y)]$
and $\mathrm{Var}_p X = \mathrm{Cov}_p(X, X)$ for the moments under the distribution $p$. The output
of the [quadratic calibration](quad-calibration.md) $f$ has variance

$$
\mathrm{Var}_p f(V) = (c_1 + 2 c_2 v_0)^2\,\mathrm{Var}_p V +
c_2^2\,\mathrm{Var}_p\bigl((V - v_0)^2\bigr) +
2\,(c_1 + 2 c_2 v_0)\,c_2\,\mathrm{Cov}_p\bigl(V, (V - v_0)^2\bigr),
$$

which keeps the variance of the remainder and the cross term, with $c_1 + 2 c_2 v_0 = f'(v_0)$; and
in every scenario $\omega$ the [remainder](quad-remainder.md) satisfies the pointwise bound

$$
\bigl|c_2\,(V(\omega) - v_0)^2\bigr| \le \frac{2\,|c_2|}{2}\,(V(\omega) - v_0)^2,
$$

the [Hessian bound](quad-calibration-vec-hessian-le.md) $2\,|c_2|$ applied scenario by scenario.
Neither conclusion needs all of these hypotheses: the variance identity holds for any real weights
summing to one, and the bound holds with equality for every voltage. The bound is pointwise; it is
not a bound on the variance terms.
