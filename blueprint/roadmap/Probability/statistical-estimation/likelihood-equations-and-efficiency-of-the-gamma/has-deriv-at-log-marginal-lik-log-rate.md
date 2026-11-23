# Derivative of the log marginal likelihood in the log rate

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For a fixed shape $a > 0$ and positive size factors $s_i > 0$, the map
$t \mapsto \ell(a, e^t)$, the [log marginal likelihood](log-marginal-lik.md) $\ell(a, b)$ as a
function of the log rate, has at every real $\beta$ the derivative $\tilde S_b(a, e^\beta)$, the
[log-rate score](rate-score-log.md) at the rate $e^\beta$. It is
[strictly concave](strict-concave-on-log-marginal-lik-log-r.md) when the sample is nonempty.
