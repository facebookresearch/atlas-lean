# Split conformal coverage

Let $n \in \mathbb{N}$, $\mu$ a probability measure on $\mathbb{R}^{n+1}$ (the law of the score vector) invariant under every coordinate permutation, and $0 \le \alpha < 1$. Then the test score is covered by the [split conformal threshold](split-conformal-threshold.md) at $k = \lceil (1 - \alpha)(n + 1) \rceil$ with probability at least $1 - \alpha$:

$$\mu\big(\omega_{n+1} \le \hat q_k(\omega)\big) \ge 1 - \alpha.$$

The sources treat $0 < \alpha < 1$; the endpoint $\alpha = 0$ (coverage $1$) is a trivial case.

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem 2.2 of the arXiv version (the one read), first part, stated for i.i.d. data and a regression fit on the first half of the sample.
- V. Vovk, A. Gammerman and G. Shafer, *Algorithmic Learning in a Random World*, Springer (2005).
