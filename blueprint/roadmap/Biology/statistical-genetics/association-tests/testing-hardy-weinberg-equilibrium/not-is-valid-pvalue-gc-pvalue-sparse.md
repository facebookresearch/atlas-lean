# No positive inflation factor makes the sparse p-value valid

In the sparse null model, with $N = 10$ individuals carrying $n_A = 2$ copies of $A$ under the
[uniform placement model](uniform-arrangements.md) $U_{10, 2}$ (the heterozygote count is then $0$
with probability $1/19$ and $2$ with probability $18/19$), the
[heterozygote-count statistic](hwe-chi-sq-of-het.md) takes only the values $10$ (no heterozygote)
and $10/81$ (two heterozygotes). For every inflation factor $\lambda > 0$, the
[genomic-control p-value](../genomic-control/gc-pvalue.md) $P(\chi^2_1 > X^2 / \lambda)$ of the
observed count is not a
[valid p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md):
at the level $t$ equal to its larger value, the p-value at $10/81$ (about $0.72$ at $\lambda = 1$),
the test rejects with probability one, although $t < 1$. The failure comes from the discreteness of
the null law. At the level $0.05$ a failure is proved only for
[$0 < \lambda \le 1$](gc-pvalue-sparse-rejection-ge.md).
