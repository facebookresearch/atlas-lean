# Prophet inequality with a single threshold

Let $n \ge 1$ and let $v_1, \dots, v_n$ be independent, nonnegative, integrable random variables observed in this order, let $V^* = \max_i v_i$ and $p = \frac12\mathbb{E}[V^*]$. The rule that stops at the first $i$ with $v_i \ge p$ and receives $v_i$ (and $0$ if there is no such $i$) has expected reward at least $\frac12\mathbb{E}[V^*]$, and so does the rule that requires $v_i > p$. The factor $\frac12$ cannot be improved: with $v_1 = 1$ and $v_2 = 1/\varepsilon$ with probability $\varepsilon \in (0, 1]$ and $0$ otherwise, no stopping rule earns more than $1$ while $\mathbb{E}[V^*] = 2 - \varepsilon$.

## Background

- [Every bounded stopping time earns at most the expected envelope at time zero](../optimal-stopping-and-the-snell-envelope/integral-stopped-value-le-integral-snell.md): optimal stopping by the Snell envelope.

## Sources

- B. Lucier, "An economic view of prophet inequalities", *ACM SIGecom Exchanges* 16(1):26–49, 2017, <https://www.sigecom.org/exchanges/volume_16/1/LUCIER.pdf>, Theorem 3.1 (attributed to Kleinberg and Weinberg) and the two-chest example in §2
