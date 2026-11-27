# Design matrix of the first $t$ regressors

For regressors $\varphi : \mathbb{N} \to \mathbb{R}^I$, indexed by an arbitrary set $I$, and $t \in \mathbb{N}$, the matrix $X$ with rows indexed by $k \in \{0, \dots, t - 1\}$, columns indexed by $I$ and entries $X(k, i) = \varphi_k(i)$; for $I = \{1, \dots, d\}$ it is the $t \times d$ matrix whose rows are $\varphi_0^\top, \dots, \varphi_{t-1}^\top$; with the responses
$Y = (y_1, \dots, y_t)$ it puts the first $t$ observations of the regression in the batch form of linear regression.
