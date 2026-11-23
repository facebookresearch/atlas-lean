# f4-ratio estimation of the admixture proportion

In a [drift model](drift-model.md) with lineage weights $w$, let $A, O, X, Y, B, C$ be populations and $\alpha \in \mathbb{R}$ with $w(X, e) = \alpha\, w(Y, e) + (1 - \alpha)\, w(C, e)$ for every edge $e$, $f_4(A, O; Y, C) = f_4(A, O; B, C)$ and $f_4(A, O; B, C) \ne 0$, for the [f4 statistic](f4.md) of the [population frequencies](freq.md). Then (Patterson et al. 2012)

$$\frac{f_4(A, O; X, C)}{f_4(A, O; B, C)} = \alpha.$$

Here $Y$ is an unsampled source lineage, sister to the sampled population $B$ relative to the $A$–$O$ path, so the ratio of two estimable statistics recovers $\alpha$, the admixture proportion when $0 \le \alpha \le 1$.

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093.
