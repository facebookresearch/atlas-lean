# Full conformal coverage

Let the law $\mu$ of the data vector $(Z_1, \dots, Z_{n+1})$, with $Z_i = (X_i, Y_i)$, be a
probability measure invariant under every coordinate permutation; an i.i.d. law is an example. Let
the score map $S$ be measurable and permutation equivariant. Then for $0 \le \alpha < 1$ the full
conformal set built from the first $n$ points at level $k = \lceil (1 - \alpha)(n + 1) \rceil$ covers
$Y_{n+1}$ at $X_{n+1}$ with probability at least $1 - \alpha$:

$$\mu\bigl(Y_{n+1} \in C_k(Z_1, \dots, Z_n; X_{n+1})\bigr) \ge 1 - \alpha.$$

Lei et al. state this for i.i.d. data and a fitting algorithm that is symmetric in the data. The
statement above assumes exchangeability only and allows any measurable equivariant score, which
includes their absolute residuals. It also allows ties, which their count (5) does not; see
[Full conformal prediction set](full-conformal-set.md). The source's range is $0 < \alpha < 1$; the
endpoint $\alpha = 0$ (the set is all of $\mathcal Y$) is a trivial case.

## Informally uses

- [Full conformal coverage event as a split conformal event](set-of-mem-full-conformal-set-eq.md): the coverage event is a split conformal event for the score vector.
- [Equivariant scores of exchangeable data are exchangeable](map-comp-perm-map-eq.md): the score vector is exchangeable.
- [Split conformal coverage](../split-conformal-prediction/of-real-one-sub-le-measure-coe-le-split.md): the lower bound for an exchangeable score vector.

## Background

- [Validity of permutation p-values](../permutation-tests/is-valid-pvalue-permutation-pvalue.md): the split conformal bound is itself the validity of the permutation p-value of the test score, $\#\{i \le n+1 : R_i \ge R_{n+1}\}/(n+1)$, which equals $1 - \pi(Y_{n+1}) + 1/(n+1)$ when there are no ties.

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem and equation numbers refer to the arXiv version, which is the one read. Theorem 2.1, first part (attributed there to Vovk).
- V. Vovk, A. Gammerman and G. Shafer, *Algorithmic Learning in a Random World*, Springer (2005).
