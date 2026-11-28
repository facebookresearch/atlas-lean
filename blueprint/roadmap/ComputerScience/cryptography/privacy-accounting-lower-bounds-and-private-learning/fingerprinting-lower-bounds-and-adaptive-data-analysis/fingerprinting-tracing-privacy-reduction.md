# Robust tracing turns accurate private marginals into a contradiction

Let $D \in \{0,1\}^{n \times d}$ be the codebook of a fingerprinting code for $n$ users of length $d$ with security $\xi$ that is robust to a $\beta$ fraction of errors (Bun, Ullman and Vadhan, Definition 3.3). Call a word $c'$ feasible for a coalition $S$ in column $j$ if $c'_j = D_{ij}$ for some $i \in S$, a condition that binds only on the columns where all members of $S$ agree, and let $F_\beta(D_S)$ be the set of words that are feasible in all but at most $\beta d$ of the $d$ columns. Robustness means that, for every coalition $S$ and every word $c'$ computed from $D_S$, the joint event that $c' \in F_\beta(D_S)$ and tracing accuses nobody has probability at most $\xi$, and tracing accuses a user outside $S$ with probability at most $\xi$. Let $M$ be an $(\varepsilon,\delta)$-differentially private algorithm that, with probability at least $3/4$, answers all but a $\beta$ fraction of the $d$ one-way marginals of its input to within error $\alpha < 1/2$. Rounding the answers gives a word that the tracer, run on the full codebook, traces to some row with probability at least $3/4 - \xi$. For a fixed row $i$, let $D_{-i}$ be $D$ with row $i$ replaced by a fixed junk row, a neighbouring database; by soundness the tracer accuses $i$ on $M(D_{-i})$ with probability at most $\xi$, so by differential privacy it accuses $i$ on $M(D)$ with probability at most $e^{\varepsilon}\xi + \delta$. Hence $n(e^{\varepsilon}\xi + \delta) \ge 3/4 - \xi$. This is impossible when $n(e^{\varepsilon}\xi + \delta) + \xi < 3/4$, in particular for $\varepsilon = O(1)$ and $\xi, \delta = o(1/n)$; since codes robust to a $1/75$ fraction of errors with $\xi = o(1/n)$ exist with $n = \tilde\Omega(\sqrt d)$ users (Theorem 3.4), no $(O(1), o(1/n))$-differentially private $M$ with $\beta \le 1/75$ exists once $d \ge \tilde\Omega(n^2)$. The conclusion is not implied by $\xi, \delta = o(1/n)$ alone when $\varepsilon$ may grow with $n$.

## Proof sketch

Accuracy within $\alpha < 1/2$ on a column where all rows agree forces the rounded answer to equal the common bit, and on a column where the rows disagree every bit is feasible. So on the event that $M$ is accurate the rounded word is infeasible in at most $\beta d$ columns and lies in $F_\beta(D)$, and by robustness the probability that $M$ is accurate yet tracing accuses nobody is at most $\xi$. The event that row $i$ is accused is a post-processing of $M$'s output together with the codebook, so by differential privacy its probability changes by at most a factor $e^{\varepsilon}$ and an additive $\delta$ between $D$ and $D_{-i}$; on $D_{-i}$ row $i$ is outside the coalition of rows actually present, so its accusation is a false accusation, of probability at most $\xi$. Summing over the $n$ rows gives the inequality.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)
- [Fingerprinting codes](../../differential-privacy/fingerprinting-codes.md)
- [Error-robust fingerprinting security](../../differential-privacy/is-error-robust-fingerprinting-secure.md)

## Proof depends on

- [Tardos codes: optimal fully collusion-resilient fingerprinting](tardos-fingerprinting-code.md)

## Sources

- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158, Definition 3.3, Theorems 3.4 and 3.5, and Lemma 2.11.
