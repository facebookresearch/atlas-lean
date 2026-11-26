# The price of approximate privacy for large families of counting queries

For datasets $D \in (\{0,1\}^d)^n$ and counting queries ("what fraction of records satisfy property $q$"), there are families $\mathcal{Q}$ of more than $nd$ counting queries such that every $(\varepsilon,\delta)$-differentially private algorithm answering all of $\mathcal{Q}$ to within error $\pm\alpha$, with $\delta = o(1/n)$, requires

$$
n \ge \tilde\Omega\!\left(\frac{\sqrt{d}\,\log|\mathcal{Q}|}{\alpha^2\,\varepsilon}\right).
$$

This is optimal up to polylogarithmic factors, being matched by the private multiplicative weights mechanism, and shows that accuracy under approximate privacy costs asymptotically more samples than accuracy alone, which needs only $O(\log|\mathcal{Q}|/\alpha^2)$.

## Proof sketch

Compose the one-way marginal lower bound with a query-composition technique: encode each record as a codeword and build queries whose answers on a structured dataset reveal the marginals of an embedded fingerprinting instance at a smaller error scale, amplifying the dependence on $\log|\mathcal{Q}|$ and on $\alpha$. The tracing argument then applies to the embedded instance.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Sample complexity of privately answering one-way marginals](private-one-way-marginals-lower-bound.md)
- [Private multiplicative weights answers exponentially many counting queries](private-multiplicative-weights.md)

## Sources

- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
