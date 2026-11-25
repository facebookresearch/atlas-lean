# Variance of an uncorrelated two-input combination

For a finite scenario type $\Omega$ and real weights $p : \Omega \to \mathbb{R}$, write $\mathbb{E}_p[X] = \sum_{\omega} p(\omega) X(\omega)$, $\operatorname{Cov}_p(X, Y) = \mathbb{E}_p[(X - \mathbb{E}_p X)(Y - \mathbb{E}_p Y)]$ and $\operatorname{Var}_p(X) = \operatorname{Cov}_p(X, X)$; the covariance matrix of a random vector $X : \Omega \to \mathbb{R}^n$ has entries $C_X(i, j) = \operatorname{Cov}_p(X_i, X_j)$.

For arbitrary real weights $p$, $X : \Omega \to \mathbb{R}^2$ and real $a_1, a_2$, if $\operatorname{Cov}_p(X_0, X_1) = 0$ then

$$\operatorname{Var}_p(a_1 X_0 + a_2 X_1) = a_1^2 \operatorname{Var}_p(X_0) + a_2^2 \operatorname{Var}_p(X_1).$$

Without the vanishing cross-covariance the term $2 a_1 a_2 \operatorname{Cov}_p(X_0, X_1)$ must be kept.
