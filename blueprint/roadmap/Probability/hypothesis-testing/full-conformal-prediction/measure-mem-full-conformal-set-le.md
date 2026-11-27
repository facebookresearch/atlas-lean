# Upper bound on full conformal coverage without ties

Under the hypotheses of [full conformal coverage](of-real-one-sub-le-measure-mem-full-conf.md), if
moreover the $n + 1$ scores $S(Z)$ are almost surely distinct, then for $0 \le \alpha < 1$ the full
conformal set at level $k = \lceil (1 - \alpha)(n + 1) \rceil$ covers $Y_{n+1}$ with probability at
most $1 - \alpha + 1/(n + 1)$. Together with the lower bound, full conformal prediction is valid and
nearly exact: its coverage lies in $[1 - \alpha, 1 - \alpha + 1/(n+1)]$.

Lei et al. assume that the fitted absolute residuals have a continuous joint distribution, and use
it only to exclude ties; almost sure distinctness is the hypothesis of the statement above. Without it the
bound fails: if all scores are equal, the coverage is $1$.

## Informally uses

- [Full conformal coverage event as a split conformal event](set-of-mem-full-conformal-set-eq.md): the coverage event is a split conformal event for the score vector.
- [Equivariant scores of exchangeable data are exchangeable](map-comp-perm-map-eq.md): the score vector is exchangeable.
- [Upper bound on split conformal coverage without ties](../split-conformal-prediction/measure-coe-le-split-conformal-threshold-2.md): the upper bound for an exchangeable score vector without ties.

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem and equation numbers refer to the arXiv version, which is the one read. Theorem 2.1, second part, and its proof in Appendix A.1.
