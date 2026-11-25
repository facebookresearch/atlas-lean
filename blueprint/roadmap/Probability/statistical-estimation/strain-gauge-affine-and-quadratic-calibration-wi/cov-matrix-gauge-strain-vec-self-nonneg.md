# Gauge strain variances are nonnegative

For a finite scenario type $\Omega$ and real weights $p : \Omega \to \mathbb{R}$, write $\mathbb{E}_p[X] = \sum_{\omega} p(\omega) X(\omega)$, $\operatorname{Cov}_p(X, Y) = \mathbb{E}_p[(X - \mathbb{E}_p X)(Y - \mathbb{E}_p Y)]$ and $\operatorname{Var}_p(X) = \operatorname{Cov}_p(X, X)$; the covariance matrix of a random vector $X : \Omega \to \mathbb{R}^n$ has entries $C_X(i, j) = \operatorname{Cov}_p(X_i, X_j)$.

Assume $p(\omega) \ge 0$ for every $\omega$ (no normalization is needed). For gains $g \in \mathbb{R}^n$ with every $g_i \ne 0$, offsets $b$, voltages $V : \Omega \to \mathbb{R}^n$ and every index $i$, the calibrated strain satisfies $\operatorname{Var}_p(\varepsilon_i) \ge 0$.
