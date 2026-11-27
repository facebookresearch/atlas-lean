# The price of approximate privacy for large families of counting queries

For datasets $D \in (\{0,1\}^d)^n$ and counting queries ("what fraction of records satisfy property $q$"), the following holds for every sufficiently small $\alpha > 0$ (bounded by an absolute constant, and $\alpha > 2^{-d/6}$), every $d \ge 6\log(1/\alpha)$ and every family size $s \ge d/\alpha^2$ (with $s \le 2^{O(d)}$). There is a family $\mathcal{Q}$ of $s$ counting queries such that every $(\varepsilon,\delta)$-differentially private algorithm with $\varepsilon = O(1)$ and $\delta = o(1/n)$ that, with probability at least $2/3$, answers every query of $\mathcal{Q}$ to within $\pm\alpha$ requires

$$
n \ge \tilde\Omega\!\left(\frac{\sqrt{d}\,\log|\mathcal{Q}|}{\alpha^2}\right).
$$

The hypotheses matter: for $d < 2\log(1/\alpha)$ the noisy histogram algorithm needs fewer samples, and for small query families answering each query with independent noise can beat the bound. In this regime the bound is optimal up to polylogarithmic factors, being matched by the private multiplicative weights mechanism, and shows that accuracy under approximate privacy costs asymptotically more samples than accuracy alone, which needs only $O(\log|\mathcal{Q}|/\alpha^2)$.

## Proof sketch

Compose the one-way marginal lower bound with a query-composition theorem: each record of a database for the composed queries combines a record of a fingerprinting instance on $d/3$ attributes with a record of a reconstruction-attack instance, and the composed queries are built so that accurate answers to them reveal accurate one-way marginals of many embedded fingerprinting instances, multiplying the sample complexities and contributing the factors $\log|\mathcal{Q}|$ and $1/\alpha^2$. The tracing argument then applies to the embedded instances, and re-identification contradicts $(O(1), o(1/n))$-differential privacy.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Sample complexity of privately answering one-way marginals](private-one-way-marginals-lower-bound.md)
- [Private multiplicative weights answers exponentially many counting queries](private-multiplicative-weights.md)

## Sources

- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158, Theorem 1.2, Theorems 5.16 and 5.17, and Lemma 2.11.
