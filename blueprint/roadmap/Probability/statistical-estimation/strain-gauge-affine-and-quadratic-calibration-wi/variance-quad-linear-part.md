# Variance of the first-order part of a quadratic calibration

For a finite scenario type $\Omega$ and real weights $p : \Omega \to \mathbb{R}$, write $\mathbb{E}_p[X] = \sum_{\omega} p(\omega) X(\omega)$, $\operatorname{Cov}_p(X, Y) = \mathbb{E}_p[(X - \mathbb{E}_p X)(Y - \mathbb{E}_p Y)]$ and $\operatorname{Var}_p(X) = \operatorname{Cov}_p(X, X)$; the covariance matrix of a random vector $X : \Omega \to \mathbb{R}^n$ has entries $C_X(i, j) = \operatorname{Cov}_p(X_i, X_j)$.

Assume $\sum_\omega p(\omega) = 1$. For voltages $V : \Omega \to \mathbb{R}$ and real $c_0, c_1, c_2, v_0$, the first-order part $\ell(v) = f(v_0) + (c_1 + 2c_2 v_0)(v - v_0)$ of $f(v) = c_0 + c_1 v + c_2 v^2$ satisfies

$$\operatorname{Var}_p(\ell(V)) = (c_1 + 2 c_2 v_0)^2\, \operatorname{Var}_p(V).$$
