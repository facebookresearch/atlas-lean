# Condition (III)

A [candidate hierarchical clustering method](hc-method.md) $T$ satisfies condition (III) if it
never merges points below the separation of the space: for every finite
[metric space](is-metric-fn.md) $(X, d)$, all $x \ne x'$ in $X$ and every $s$ with
$s \le d(a, b)$ for all $a \ne b$, we have $s \le T(X, d)(x, x')$ (Carlsson and Mémoli, JMLR 11
(2010), Thm. 18 (III), $u(x, x') \ge \mathrm{sep}(X, d)$).
