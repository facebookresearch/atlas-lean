# Approximately private release of quadratically many marginals is impossible

There are absolute constants $C, \gamma_0 > 0$ such that the following holds for every sufficiently large $n$ and every $\delta$ with $2^{-\gamma_0 n} \le \delta \le 1/n^{1+\gamma}$ for a fixed constant $\gamma > 0$ (the implied constant $C$ depending on $\gamma$). If $d \ge C n^2/\log(1/\delta)$, no $(1, \delta)$-differentially private algorithm $M : \{\pm1\}^{n \times d} \to [-1,1]^d$ answers the $d$ one-way marginals with expected $\ell_1$ error at most $d/10$ on every database. Equivalently, under privacy parameters in this regime the number of one-way marginals that can be released with constant average error is $O(n^2/\log(1/\delta))$, hence $O(n^2)$, whereas without privacy all marginals of any number $d$ can be released exactly; the Gaussian mechanism, at any fixed privacy parameter $\varepsilon < 1$, releases $d = \Theta(n^2/\log(1/\delta))$ marginals with constant average error, so this is tight for average error. With worst-case accuracy, robust fingerprinting codes give the related statement that no $(O(1), o(1/n))$-differentially private algorithm answers all but a small constant fraction of $d \ge \tilde\Omega(n^2)$ one-way marginals within $1/3$ with probability $2/3$. A choice such as $\delta = 1/(n \log n)$ is $o(1/n)$ but lies outside the first regime, so it is covered only by the second statement.

## Proof sketch

Take $\varepsilon = 1$ and $\alpha = 1/10$ in the one-way marginal lower bound $n \ge \Omega\bigl(\sqrt{d\log(1/\delta)}/(\alpha\varepsilon)\bigr)$, valid for $\delta$ in the stated range and expected $\ell_1$ error $\alpha d$; rearranging gives $d \le O(n^2/\log(1/\delta))$. The Gaussian mechanism with noise of standard deviation $O(\sqrt{d\log(1/\delta)}/(n\varepsilon))$ per marginal has expected error of that order on each marginal, which is constant when $d = O(n^2/\log(1/\delta))$. The worst-case statement is the tracing reduction with robust codes of length $\tilde O(n^2)$.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Sample complexity of privately answering one-way marginals](private-one-way-marginals-lower-bound.md)
- [Robust tracing turns accurate private marginals into a contradiction](fingerprinting-tracing-privacy-reduction.md)
- [The Gaussian mechanism](../../differential-privacy/gaussian-mechanism-differentially-privat.md)

## Sources

- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158, Theorem 3.5 and Corollary 3.6.
- T. Steinke, J. Ullman, "Between Pure and Approximate Differential Privacy", Journal of Privacy and Confidentiality 7 (2017), arXiv:1501.06095, Theorems 1.1 and 3.1.
