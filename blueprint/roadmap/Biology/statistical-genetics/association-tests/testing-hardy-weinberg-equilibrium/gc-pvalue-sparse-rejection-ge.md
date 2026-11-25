# Genomic control with factor at most one stays anti-conservative

In the sparse null model, with $N = 10$ individuals carrying $n_A = 2$ copies of $A$ under the
[uniform placement model](uniform-arrangements.md) $U_{10, 2}$ (the heterozygote count is then $0$
with probability $1/19$ and $2$ with probability $18/19$), for every inflation factor
$0 < \lambda \le 1$ the level-$0.05$ test based on the
[genomic-control p-value](../genomic-control/gc-pvalue.md) $P(\chi^2_1 > X^2 / \lambda)$ of the
[heterozygote-count statistic](hwe-chi-sq-of-het.md) rejects with probability at least
$1/19 > 0.05$. Clipped genomic control uses a factor of at least $1$, so of this range only its
endpoint $\lambda = 1$ occurs after clipping, where the test still rejects with probability at least
$1/19$; a factor below $1$ inflates the statistic and makes rejection easier.
