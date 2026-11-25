# Variance of a combination of two correlated gauges

For a finite scenario type $\Omega$ and real weights $p : \Omega \to \mathbb{R}$, write $\mathbb{E}_p[X] = \sum_{\omega} p(\omega) X(\omega)$, $\operatorname{Cov}_p(X, Y) = \mathbb{E}_p[(X - \mathbb{E}_p X)(Y - \mathbb{E}_p Y)]$ and $\operatorname{Var}_p(X) = \operatorname{Cov}_p(X, X)$; the covariance matrix of a random vector $X : \Omega \to \mathbb{R}^n$ has entries $C_X(i, j) = \operatorname{Cov}_p(X_i, X_j)$.

Assume $\sum_{\omega} p(\omega) = 1$. For two gauges with gains $g_0, g_1 \ne 0$, offsets $b$, voltages $V : \Omega \to \mathbb{R}^2$ and real $a_1, a_2$, the combination $a_1 \varepsilon_0 + a_2 \varepsilon_1$ of the calibrated strains has variance

$$\frac{a_1^2\, \operatorname{Var}_p(V_0)}{g_0^2} + \frac{a_2^2\, \operatorname{Var}_p(V_1)}{g_1^2} + \frac{2\, a_1 a_2\, \operatorname{Cov}_p(V_0, V_1)}{g_0\, g_1}.$$
