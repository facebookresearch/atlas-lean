# Robust tracing turns accurate private marginals into a contradiction

Let $D \in \{0,1\}^{n \times d}$ be the codebook of a robust fingerprinting code for $n$ users of length $d$ (tolerating a small constant fraction of columns violating the marking assumption), and let $M$ be an $(\varepsilon,\delta)$-differentially private algorithm that, with probability at least $3/4$, answers all $d$ one-way marginals of its input to within error $\alpha < 1/2$. Rounding the answers gives a pirate word for the coalition of all $n$ rows, so the tracer accuses some row with probability at least $3/4 - \xi$; on the other hand, privacy implies that every fixed row is accused with probability at most $e^{\varepsilon}\xi + \delta$, since removing that row (replacing it with an independent codeword) leaves the accusation probability below $\xi$. Hence $n(e^{\varepsilon}\xi + \delta) \ge 3/4 - \xi$, which fails for $\xi, \delta = o(1/n)$, so such $M$ cannot exist for code lengths $d \ge \tilde\Omega(n^2)$.

## Proof sketch

Accuracy within $\alpha < 1/2$ on a column where all rows agree forces the rounded answer to equal the common bit, so the rounded answer satisfies the marking assumption except on the few columns tolerated by robustness. The probability that row $i$ is accused is a function of $M$'s output, so by differential privacy it changes by at most a factor $e^{\varepsilon}$ and an additive $\delta$ when row $i$ is replaced; after replacement the accusation is a false accusation, of probability at most $\xi$. Summing over the $n$ rows gives the inequality.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Fingerprinting codes](../differential-privacy/fingerprinting-codes.md)

## Proof depends on

- [Tardos codes: optimal fully collusion-resilient fingerprinting](tardos-fingerprinting-code.md)

## Sources

- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
