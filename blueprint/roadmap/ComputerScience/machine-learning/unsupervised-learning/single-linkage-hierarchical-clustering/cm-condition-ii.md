# Condition (II), functoriality

A [candidate hierarchical clustering method](hc-method.md) $T$ satisfies condition (II) if for
all finite [metric spaces](is-metric-fn.md) $(X, d_X)$ and $(Y, d_Y)$ and every map
$\varphi : X \to Y$ with $d_Y(\varphi x, \varphi x') \le d_X(x, x')$ for all $x, x'$, the outputs
$u_X = T(X, d_X)$ and $u_Y = T(Y, d_Y)$ satisfy $u_Y(\varphi x, \varphi x') \le u_X(x, x')$ for all
$x, x'$ (Carlsson and Mémoli, JMLR 11 (2010), Thm. 18 (II)).
