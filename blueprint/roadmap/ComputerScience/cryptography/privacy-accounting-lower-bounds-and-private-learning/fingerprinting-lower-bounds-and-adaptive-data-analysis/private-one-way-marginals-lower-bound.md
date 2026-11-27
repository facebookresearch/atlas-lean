# Sample complexity of privately answering one-way marginals

Let $D \in \{\pm 1\}^{n \times d}$ and consider its $d$ one-way marginals $q_j(D) = \frac{1}{n}\sum_i D_{ij}$, forming the vector $\overline{D} \in [-1,1]^d$. Steinke and Ullman's main theorem fixes the accuracy and the privacy loss: if $M : \{\pm1\}^{n \times d} \to [-1,1]^d$ is $(1,\delta)$-differentially private with expected $\ell_1$ error $\mathbb{E}_M \lVert M(D) - \overline{D} \rVert_1 \le d/10$ for every $D$, where $2^{-\Omega(n)} \le \delta \le 1/n^{1+\Omega(1)}$ and $n$ is sufficiently large, then $d \le O(n^2/\log(1/\delta))$. General accuracy and privacy loss reduce to this case. Let $\alpha, \varepsilon, \delta \in (0, 1/10]$ and let $M$ be $(\varepsilon,\delta)$-differentially private with $\mathbb{E}_M \lVert M(D) - \overline{D} \rVert_1 \le \alpha d$ for every $D$. Then $M$ yields a $(1, \delta/\varepsilon)$-differentially private mechanism with expected $\ell_1$ error at most $d/10$ on databases of $n' = \Theta(\alpha\varepsilon n)$ rows, so if $n'$ is sufficiently large and $2^{-\Omega(n')} \le \delta/\varepsilon \le 1/n'^{1+\Omega(1)}$, then

$$
n \ge \Omega\!\left(\frac{\sqrt{d \log(\varepsilon/\delta)}}{\alpha\,\varepsilon}\right).
$$

The hypotheses concern $n' = \Theta(\alpha\varepsilon n)$, not $n$: for $d = 1$, $\varepsilon = 1/10$, $\alpha = 20/n$ and $\delta = e^{-\sqrt n}$ the Laplace mechanism, clipped to $[-1,1]$, has expected error at most $20/n = \alpha d$, while the display would demand $n \ge \Omega(n^{5/4})$; here $n' = \Theta(1)$. When $\log(\varepsilon/\delta) = \Theta(\log(1/\delta))$ the bound is matched up to constants by the Gaussian mechanism, and the range of $\delta$ is necessary: the Laplace mechanism is $(\varepsilon, 0)$-differentially private with this accuracy once $n \ge O(d/(\alpha\varepsilon))$. The earlier bound $n \ge \tilde\Omega(\sqrt{d}/(\alpha\varepsilon))$ for $\delta = o(1/n)$ followed from the tracing reduction with robust Tardos codes.

## Proof sketch

By the reduction above it suffices to treat $\varepsilon = 1$ and expected $\ell_1$ error at most $d/10$, with $n$ sufficiently large and $\delta$ in the stated range, and to show $d \le O(n^2/\log(1/\delta))$. Let $k = \Theta(\log(1/\delta))$, which is at most $n/200$ by the lower limit on $\delta$ and $\Omega(\log(1/\delta))$ by the upper limit. From $M$ build a mechanism $M_k$ on databases of $n_k = \lfloor n/k \rfloor$ rows: repeat the input $k$ times, pad with rows of $1$s, and run $M$. By group privacy $M_k$ is $(k, \frac{e^k - 1}{e-1}\delta)$-differentially private, and its marginals differ from the input's by at most $2k/n$, so $M_k$ is still accurate on average. Run an $\ell_1$ fingerprinting code for $n_k$ users that is $\delta$-sound, which exists with length $O(n_k^2 \log(1/\delta))$. Accuracy forces the tracer to accuse some row of $M_k$'s input with probability at least $1/12$, so some row is accused with probability at least $1/(12 n_k)$; soundness on the neighbouring database with that row replaced by a fixed row, together with privacy, bounds this probability by $e^k \delta + \frac{e^k - 1}{e-1}\delta < e^{k+1}\delta$, a contradiction for the chosen $k$ unless $d < O(n_k^2 \log(1/\delta)) = O(n^2/\log(1/\delta))$.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Robust tracing turns accurate private marginals into a contradiction](fingerprinting-tracing-privacy-reduction.md)
- [Tardos codes: optimal fully collusion-resilient fingerprinting](tardos-fingerprinting-code.md)
- [Group privacy for approximate differential privacy](../../k-fold-adaptive-composition-and-group-privacy/is-approx-dp-group-privacy.md)
- [The Gaussian mechanism](../../differential-privacy/gaussian-mechanism-differentially-privat.md)

## Sources

- T. Steinke, J. Ullman, "Between Pure and Approximate Differential Privacy", Journal of Privacy and Confidentiality 7 (2017), arXiv:1501.06095, Theorems 1.1, 3.1 and 3.3 and Fact 2.3.
- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
