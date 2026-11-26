# Differential privacy answers quadratically many adaptive statistical queries efficiently

Let $D$ be an unknown distribution on $\mathcal{X}$ and $S \sim D^n$. For every $\alpha, \beta > 0$ there is a computationally efficient mechanism that answers any $k$ adaptively chosen statistical queries $\psi_j : \mathcal{X} \to [0,1]$ with answers $a_j$ satisfying $|a_j - \mathbb{E}_D[\psi_j]| \le \alpha$ for all $j$ with probability $1 - \beta$, provided

$$
n = \tilde O\!\left(\frac{\sqrt{k}}{\alpha^2}\right),
$$

whereas the empirical mean, valid for non-adaptive queries with $n = O(\log k/\alpha^2)$, can be wrong after $O(n)$ adaptive queries. With unbounded computation, an exponential number of adaptive queries in $n$ can be answered accurately (via private multiplicative weights).

## Proof sketch

Answer each query with the Gaussian mechanism at noise level about $\sqrt{k}/(\alpha n)$, so that the whole interaction is $(\varepsilon, \delta)$-DP with $\varepsilon \approx \alpha$ by advanced composition, and sample-accurate. The transfer theorem says that a differentially private, sample-accurate mechanism is population-accurate: privacy makes the dataset and the adaptively chosen queries nearly independent, so empirical answers generalize. Solving for $n$ gives the bound.

## Depends on

- [Transfer theorem for adaptive data analysis](../differential-privacy/differentially-private-transfer.md)
- [Advanced composition](../differential-privacy/differentially-private-pi-advanced.md)
- [The Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md)
- [Private multiplicative weights answers exponentially many counting queries](private-multiplicative-weights.md)

## Proof depends on

- [Transfer theorem for adaptive data analysis](../differential-privacy/differentially-private-transfer.md)
- [Advanced composition](../differential-privacy/differentially-private-pi-advanced.md)
- [The Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md)
- [Private multiplicative weights answers exponentially many counting queries](private-multiplicative-weights.md)

## Sources

- C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, "Preserving Statistical Validity in Adaptive Data Analysis", STOC (2015), arXiv:1411.2664.
- R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, "Algorithmic Stability for Adaptive Data Analysis", STOC (2016), arXiv:1511.02513.
