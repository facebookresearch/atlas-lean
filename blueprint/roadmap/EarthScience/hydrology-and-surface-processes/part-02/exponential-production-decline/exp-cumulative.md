# Cumulative production under exponential decline

For real numbers $q_i$, $D$ and $t$, let

$$N(t) = \frac{q_i - q(t)}{D}, \qquad q(t) = q_i e^{-D t} ,$$

read as $0$ when $D = 0$. For $D \neq 0$ it is the cumulative production up to time $t$ under the
exponential decline $q(t)$: it [starts at $0$](exp-cumulative-zero.md) and
[its derivative is $q(t)$](exp-cumulative-has-deriv-at.md); the physical regime is $D > 0$. With no
decline the cumulative production is $q_i t$, the [constant-rate law](const-cumulative.md), not
$N(t)$.
