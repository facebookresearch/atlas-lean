# Nonnegative weights give nonnegative strain variances

Let $\Omega$ be a finite set of scenarios with nonnegative weights $p(\omega) \ge 0$, of any total,
and let $V(\omega) \in \mathbb{R}^n$ be the voltage vector of $n$ gauges in scenario $\omega$. For
gains $g_1, \dots, g_n$, all nonzero, offsets $b$ and each channel $i$, the weighted variance of the
[strain](gauge-strain-vec.md) $\varepsilon_i = (V_i - b_i)/g_i$, which is the diagonal entry $i$ of
the weighted strain covariance matrix, is nonnegative:

$$
\sum_{\omega} p(\omega)\,\bigl(\varepsilon_i(\omega) - E_p\varepsilon_i\bigr)^2 \ge 0,
\qquad E_p\varepsilon_i = \sum_{\omega} p(\omega)\,\varepsilon_i(\omega).
$$

The nonnegativity of the weights is what matters: the signed weights $2$ and $-1$ on two scenarios
also sum to one, and for one gauge of gain $1$ and offset $0$ reading the voltages $0$ and $1$ they
give the value $-2$.
