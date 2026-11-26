# Sample complexity of privately answering one-way marginals

Let $D \in \{\pm 1\}^{n \times d}$ and consider its $d$ one-way marginals $q_j(D) = \frac{1}{n}\sum_i D_{ij}$. Every $(\varepsilon,\delta)$-differentially private algorithm that answers all one-way marginals to within average error $\alpha$ requires

$$
n \ge \Omega\!\left(\frac{\sqrt{d \log(1/\delta)}}{\alpha\,\varepsilon}\right),
$$

for $\delta$ in the range between $2^{-d}$ and $1/n^{1+\Omega(1)}$, which is optimal up to constants (matched by the Gaussian mechanism) and interpolates smoothly between approximate and pure privacy ($d/(\alpha\varepsilon)$). The earlier bound $n \ge \tilde\Omega(\sqrt{d}/(\alpha\varepsilon))$ followed from the tracing reduction with Tardos codes.

## Proof sketch

Draw the dataset from a product distribution with column biases from a smooth prior and apply a fingerprinting lemma: for any estimator $f$ of a column mean $p$ from $n$ samples, $\mathbb{E}\big[f(x)\sum_i (x_i - p)\big]$ is bounded below by a constant minus a multiple of the estimator's error. Summed over columns, accuracy forces the total correlation between the output and the rows to be $\Omega(d)$, while privacy (with group-like amplification using $\log(1/\delta)$) bounds the expected correlation of each single row with the output by $O\big(\varepsilon\,\mathbb{E}|\text{correlation}| + \delta\sqrt{d}\big)$, which is of order $\varepsilon\alpha\sqrt{d}$; comparing the sum over $n$ rows with $\Omega(d)$ gives the bound. The optimal $\delta$-dependence comes from biasing the prior toward rare columns.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Robust tracing turns accurate private marginals into a contradiction](fingerprinting-tracing-privacy-reduction.md)
- [The Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md)

## Sources

- T. Steinke, J. Ullman, "Between Pure and Approximate Differential Privacy", Journal of Privacy and Confidentiality 7 (2017), arXiv:1501.06095.
- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
