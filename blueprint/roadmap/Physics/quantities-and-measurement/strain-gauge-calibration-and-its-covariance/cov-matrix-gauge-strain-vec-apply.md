# Entrywise strain covariance, for weights summing to one

Let $\Omega$ be a finite set of scenarios with real weights $p(\omega)$ summing to one, let
$V(\omega) \in \mathbb{R}^n$ be the voltage vector of $n$ gauges in scenario $\omega$, and write
$E_p X = \sum_{\omega} p(\omega)\,X(\omega)$ and
$\mathrm{Cov}_p(X, Y) = E_p[(X - E_p X)(Y - E_p Y)]$. For gains $g_1, \dots, g_n$, all nonzero,
offsets $b$ and all channels $i$ and $j$, including $i \ne j$, the [strains](gauge-strain-vec.md)
$\varepsilon_i = (V_i - b_i)/g_i$ satisfy

$$
\mathrm{Cov}_p(\varepsilon_i, \varepsilon_j) = \frac{\mathrm{Cov}_p(V_i, V_j)}{g_i\,g_j}:
$$

the cross-channel covariances are kept, not dropped. The weights may be signed; when they are also
nonnegative, these are covariances under the probability distribution $p$ on the scenarios. Total
weight one is needed: with weights $1$ and $1$ on two scenarios, one gauge of gain $1$ and offset
$1$, and voltage $0$ in both scenarios, the left side is $2$ and the right side is $0$.
