# Covariance matrix of calibrated gauge strains

For a finite scenario type $\Omega$ and real weights $p : \Omega \to \mathbb{R}$, write $\mathbb{E}_p[X] = \sum_{\omega} p(\omega) X(\omega)$, $\operatorname{Cov}_p(X, Y) = \mathbb{E}_p[(X - \mathbb{E}_p X)(Y - \mathbb{E}_p Y)]$ and $\operatorname{Var}_p(X) = \operatorname{Cov}_p(X, X)$; the covariance matrix of a random vector $X : \Omega \to \mathbb{R}^n$ has entries $C_X(i, j) = \operatorname{Cov}_p(X_i, X_j)$.

Assume $\sum_{\omega} p(\omega) = 1$. For gains $g \in \mathbb{R}^n$ with every $g_i \ne 0$, offsets $b$ and voltages $V : \Omega \to \mathbb{R}^n$, the strain vectors $\varepsilon(\omega)_i = (V(\omega)_i - b_i)/g_i$ have covariance matrix

$$C_\varepsilon = G\, C_V\, G^{\mathsf{T}}, \qquad G = \operatorname{diag}(g_0^{-1}, \dots, g_{n-1}^{-1}).$$
