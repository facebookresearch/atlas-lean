# Differential privacy answers quadratically many adaptive statistical queries efficiently

Let $D$ be an unknown distribution on $\mathcal{X}$ and $S \sim D^n$. For every $\alpha, \beta > 0$ there is a computationally efficient mechanism that answers any $k$ adaptively chosen statistical queries $\psi_j : \mathcal{X} \to [0,1]$ with answers $a_j$ satisfying $|a_j - \mathbb{E}_D[\psi_j]| \le \alpha$ for all $j$ with probability $1 - \beta$, provided

$$
n = \tilde O\!\left(\frac{\sqrt{k}}{\alpha^2}\right),
$$

whereas the empirical mean, valid for non-adaptive queries with $n = O(\log k/\alpha^2)$, can be wrong after $O(n)$ adaptive queries. The bound above does not depend on $\mathcal{X}$. If $\mathcal{X}$ is finite, a computationally inefficient mechanism (private multiplicative weights) answers $k$ adaptive queries to the same accuracy with a sample size $n$ polynomial in $\log k$, $\log |\mathcal{X}|$, $1/\alpha$ and $\log(1/\beta)$ (Dwork et al., Theorem 1); so for a fixed finite universe exponentially many queries in a power of $n$ can be answered. This guarantee grows with $\log |\mathcal{X}|$ and is not dimension-independent: unbounded computation alone does not suffice, since over a universe of sufficiently high dimension relative to $n$ even a computationally unbounded mechanism fails after $O(n^2)$ adaptive queries (Steinke and Ullman, Theorem 1.2 and Section 3.6, in dimension $d = O(n^2)$).

## Proof sketch

Answer each query with the Gaussian mechanism at noise level about $\sqrt{k}/(\alpha n)$ up to logarithmic factors, so that the whole interaction is $(\varepsilon, \delta)$-differentially private with $\varepsilon \approx \alpha$ by advanced composition and, by Gaussian tail bounds, $(\alpha, \beta)$-sample accurate. A transfer theorem for approximately differentially private, sample-accurate interactions with many adaptively chosen queries, holding with high probability, then makes the answers population-accurate up to $O(\alpha)$; the single-query, pure-privacy transfer theorem does not suffice for this transcript of Gaussian answers. Solving for $n$ gives the bound.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Posterior-based proof of the transfer theorem for adaptive data analysis](posterior-transfer-theorem.md)
- [Advanced composition](../../differential-privacy/differentially-private-pi-advanced.md)
- [The Gaussian mechanism](../../differential-privacy/gaussian-mechanism-differentially-privat.md)
- [Private multiplicative weights answers exponentially many counting queries](private-multiplicative-weights.md)

## Sources

- C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, "Preserving Statistical Validity in Adaptive Data Analysis", STOC (2015), arXiv:1411.2664.
- R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, "Algorithmic Stability for Adaptive Data Analysis", STOC (2016), arXiv:1511.02513.
- T. Steinke, J. Ullman, "Interactive Fingerprinting Codes and the Hardness of Preventing False Discovery", COLT (2015), arXiv:1410.1228.
