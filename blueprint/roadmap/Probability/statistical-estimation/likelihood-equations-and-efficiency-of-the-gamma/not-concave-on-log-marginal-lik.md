# The log marginal likelihood is not jointly concave

For a single observation with count $0$ at size factor $1$, the
[log marginal likelihood](log-marginal-lik.md) is $\ell(a, b) = a \log\bigl(b / (b + 1)\bigr)$ for
$a, b > 0$, and it is not concave on $(0, \infty)^2$: it violates midpoint concavity between
$(1, 1)$ and $(3, 3)$, $\ell(2, 2) < (\ell(1, 1) + \ell(3, 3)) / 2$, because $2^{11} < 3^7$.
Concavity holds in the [shape](concave-on-log-marginal-lik-shape.md) and in the
[log rate](strict-concave-on-log-marginal-lik-log-r.md) separately.
