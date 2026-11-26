# Prophet inequality with a single threshold

Let $n \ge 1$ and let $v_1, \dots, v_n$ be independent, nonnegative almost surely, integrable random variables observed in this order. Let $V^* = \max_i v_i$ and $p = \frac12\mathbb{E}[V^*]$. For any measurable acceptance set $A$ with $(p,\infty)\subseteq A\subseteq [p,\infty)$, the [payoff from the first accepted observation](single-threshold-reward.md) has expectation at least $p$. In particular, the bound holds whether the rule accepts or rejects an observation equal to $p$.

The [two-prize example](single-threshold-prophet-two-prize-sharp.md) shows that the factor $1/2$ cannot be improved.

## Background

- [Every bounded stopping time earns at most the expected envelope at time zero](../optimal-stopping-and-the-snell-envelope/integral-stopped-value-le-integral-snell.md): optimal stopping by the Snell envelope.

## Sources

- B. Lucier, "An economic view of prophet inequalities", *ACM SIGecom Exchanges* 16(1):26–49, 2017, <https://www.sigecom.org/exchanges/volume_16/1/LUCIER.pdf>, Theorem 3.1 (attributed to Kleinberg and Weinberg) and the two-chest example in §2
