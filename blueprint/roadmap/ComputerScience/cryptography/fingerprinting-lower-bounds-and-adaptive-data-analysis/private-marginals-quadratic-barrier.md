# Approximately private release of quadratically many marginals is impossible

There is an absolute constant $c > 0$ such that for every $n$ and $d \ge c^{-1} n^2$, no $(1, o(1/n))$-differentially private algorithm on datasets $D \in \{\pm1\}^{n \times d}$ answers all $d$ one-way marginals to within average error $c$ with probability at least $3/4$. Equivalently, under constant privacy parameters the number of one-way marginals that can be released with constant error is $O(n^2)$, whereas without privacy all marginals of any number $d$ can be released exactly, and with the Gaussian mechanism $\tilde O(n^2)$ marginals can be released with constant error.

## Proof sketch

Set $\varepsilon = 1$ and $\alpha = c$ in the one-way marginal lower bound $n \ge \Omega\big(\sqrt{d\log(1/\delta)}/(\alpha\varepsilon)\big)$; with $\delta = o(1/n)$ the right side is at least $\Omega(\sqrt{d})$, so $d \le O(n^2)$. The Gaussian mechanism with noise $\sqrt{d\log(1/\delta)}/(n\varepsilon)$ per marginal gives constant error when $d = \tilde O(n^2)$.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Sample complexity of privately answering one-way marginals](private-one-way-marginals-lower-bound.md)
- [The Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md)

## Sources

- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
- T. Steinke, J. Ullman, "Between Pure and Approximate Differential Privacy", Journal of Privacy and Confidentiality 7 (2017), arXiv:1501.06095.
