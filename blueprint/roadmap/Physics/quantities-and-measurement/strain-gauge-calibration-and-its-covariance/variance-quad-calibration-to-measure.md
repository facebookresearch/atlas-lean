# Output variance split under a probability mass function

Let $q$ be a probability mass function on a finite set $\Omega$ of scenarios, carrying a
$\sigma$-algebra in which every singleton is measurable, and let $\mu_q$ be the probability measure
of $q$. For scenario voltages $V : \Omega \to \mathbb{R}$ and real $c_0$, $c_1$, $c_2$ and $v_0$,
with $f$ the [quadratic calibration](quad-calibration.md), $L_{v_0}$ its
[first-order part](quad-linear-part.md) and $R_{v_0}$ its [remainder](quad-remainder.md) at $v_0$,

$$
\mathrm{Var}_{\mu_q} f(V) = \mathrm{Var}_{\mu_q} L_{v_0}(V) +
2\,\mathrm{Cov}_{\mu_q}\bigl(L_{v_0}(V), R_{v_0}(V)\bigr) + \mathrm{Var}_{\mu_q} R_{v_0}(V).
$$

Here $\mathrm{Var}_{\mu_q}$ and $\mathrm{Cov}_{\mu_q}$ are the variance and covariance of random
variables under $\mu_q$, $\mathrm{Var}_{\mu_q} X = \int (X - \mathbb{E}X)^2\,d\mu_q$ and
$\mathrm{Cov}_{\mu_q}(X, Y) = \int (X - \mathbb{E}X)(Y - \mathbb{E}Y)\,d\mu_q$, with $\mathbb{E}$
the expectation under $\mu_q$. On a finite space whose singletons are measurable every function is
square-integrable, which the split uses.
