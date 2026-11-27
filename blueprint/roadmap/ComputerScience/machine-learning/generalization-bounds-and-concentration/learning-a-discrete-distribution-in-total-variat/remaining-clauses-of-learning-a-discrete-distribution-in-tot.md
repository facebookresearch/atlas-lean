# High-probability sample complexity of learning a discrete distribution

This node collects the high-probability sample-complexity clauses for learning a distribution $p$ on a
$k$-element set from $n$ independent samples in total variation. The expectation bound for the empirical
distribution, $\mathbb{E}\, d_{TV}(\hat p_n, p) \le \tfrac12 \sqrt{k/n}$ for $n \ge 1$, is a separate result and is not part of
this node.

## Expansion

A sound expansion has separate pages for:

1. **Upper bound,** with explicit constants on the split page. For every $k \ge 1$, $\varepsilon \in (0,1]$ and $\delta \in (0,1)$, some
   $n = O\bigl((k + \log(1/\delta))/\varepsilon^2\bigr)$ samples suffice for the empirical distribution
   to satisfy $d_{TV}(\hat p_n, p) \le \varepsilon$ with probability at least $1 - \delta$ (expectation
   bound plus a bounded-differences concentration inequality).
2. **Lower bound,** with explicit constants on the split page. For $k \ge 2$ and $\varepsilon$, $\delta$ below absolute constants, every estimator
   needs $\Omega\bigl((k + \log(1/\delta))/\varepsilon^2\bigr)$ samples for this guarantee on all
   distributions over $k$ elements (Assouad's lemma for the $k/\varepsilon^2$ term; estimating the bias
   of a coin for the $\log(1/\delta)/\varepsilon^2$ term). The restriction $k \ge 2$ is needed: for
   $k = 1$ the distribution is known and no samples are required.

## Sources

- C. L. Canonne, *A short note on learning discrete distributions*, arXiv:2002.11457, Theorem 1 and its
  proof (upper bound via the empirical distribution; lower bound via Assouad's lemma and coin-bias
  estimation). <https://arxiv.org/abs/2002.11457>
