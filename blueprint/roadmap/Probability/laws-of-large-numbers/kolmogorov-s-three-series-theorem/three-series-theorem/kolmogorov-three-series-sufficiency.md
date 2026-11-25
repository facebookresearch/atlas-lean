# Kolmogorov's three-series theorem (sufficiency direction)

Let $X_0, X_1, \dots$ be
independent real random variables on a probability space $(\Omega, P)$, fix $A > 0$, and write
$Y_n = X_n \mathbf{1}_{\{|X_n| \le A\}}$ for the truncations. If
$\sum_n P(|X_n| > A) < \infty$, the series $\sum_n E[Y_n]$ converges absolutely, and
$\sum_n \operatorname{Var}(Y_n) < \infty$, then there is a function $S : \Omega \to \mathbb{R}$
with $\sum_{i < n} X_i(\omega) \to S(\omega)$ as $n \to \infty$ for almost every $\omega$; that
is, $\sum_n X_n$ converges almost surely.

The classical theorem only requires the series $\sum_n E[Y_n]$ to converge; here it must converge
absolutely.
