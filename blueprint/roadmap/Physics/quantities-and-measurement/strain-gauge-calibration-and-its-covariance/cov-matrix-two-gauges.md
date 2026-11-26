# Variance of a combination of two gauge strains, cross term included

Let $\Omega$ be a finite set of scenarios with real weights $p(\omega)$ summing to one, and let two
gauges with nonzero gains $g_1$, $g_2$ and offsets $b_1$, $b_2$ read the voltages $V_1(\omega)$ and
$V_2(\omega)$, with [strains](gauge-strain-vec.md) $\varepsilon_k = (V_k - b_k)/g_k$. Write
$E_p X = \sum_{\omega} p(\omega)\,X(\omega)$, $\mathrm{Cov}_p(X, Y) = E_p[(X - E_p X)(Y - E_p Y)]$
and $\mathrm{Var}_p X = \mathrm{Cov}_p(X, X)$. For real coefficients $a_1$ and $a_2$,

$$
\mathrm{Var}_p(a_1\varepsilon_1 + a_2\varepsilon_2)
= \frac{a_1^2\,\mathrm{Var}_p V_1}{g_1^2} + \frac{a_2^2\,\mathrm{Var}_p V_2}{g_2^2} +
\frac{2\,a_1 a_2\,\mathrm{Cov}_p(V_1, V_2)}{g_1\,g_2}.
$$

The cross term is kept: the voltages need not be uncorrelated. The weights may be signed; when they
are also nonnegative, these are the variance and covariance under the probability distribution $p$
on the scenarios.
