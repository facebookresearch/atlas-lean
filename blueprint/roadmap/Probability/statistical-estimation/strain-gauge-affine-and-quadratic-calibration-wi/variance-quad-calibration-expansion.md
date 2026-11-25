# Variance of a quadratic calibration with cross term

For a finite scenario type $\Omega$ and real weights $p : \Omega \to \mathbb{R}$, write $\mathbb{E}_p[X] = \sum_{\omega} p(\omega) X(\omega)$, $\operatorname{Cov}_p(X, Y) = \mathbb{E}_p[(X - \mathbb{E}_p X)(Y - \mathbb{E}_p Y)]$ and $\operatorname{Var}_p(X) = \operatorname{Cov}_p(X, X)$; the covariance matrix of a random vector $X : \Omega \to \mathbb{R}^n$ has entries $C_X(i, j) = \operatorname{Cov}_p(X_i, X_j)$.

For arbitrary real weights $p$ (no positivity or normalization), voltages $V : \Omega \to \mathbb{R}$ and real $c_0, c_1, c_2, v_0$, let $f(v) = c_0 + c_1 v + c_2 v^2$, $\ell(v) = f(v_0) + (c_1 + 2c_2 v_0)(v - v_0)$ and $R(v) = c_2 (v - v_0)^2$. Then

$$\operatorname{Var}_p(f(V)) = \operatorname{Var}_p(\ell(V)) + \operatorname{Var}_p(R(V)) + 2\, \operatorname{Cov}_p(\ell(V), R(V)).$$
