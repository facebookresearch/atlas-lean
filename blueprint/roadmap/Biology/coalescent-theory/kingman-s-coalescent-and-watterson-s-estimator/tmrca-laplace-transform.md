# Laplace transform of the time to the most recent common ancestor in Kingman's coalescent

In Kingman's coalescent with $n \ge 2$ lineages the holding times $T_k \sim \mathrm{Exp}\bigl(\binom k2\bigr)$, $2 \le k \le n$, are independent (Tavaré 2004, Sec. 2.3), so the [time to the most recent common ancestor](tmrca.md) $T_{\mathrm{MRCA},n} = \sum_{k=2}^n T_k$ has

$$E\bigl[e^{-sT_{\mathrm{MRCA},n}}\bigr] = \prod_{k=2}^n \frac{\binom k2}{\binom k2 + s}, \qquad s > -1,$$

and $E[e^{-sT_{\mathrm{MRCA},n}}] = \infty$ for $s \le -1$, since the smallest rate is $\binom22 = 1$. For every $s > -1$, as $n \to \infty$ these transforms converge to the convergent infinite product $\prod_{k \ge 2}\binom k2/(\binom k2 + s)$ (convergent because $\sum_k s/\binom k2$ converges), which is the Laplace transform of the [time to the most recent common ancestor of the whole population](time-to-the-most-recent-common-ancestor-of-the-w.md) $T_\infty = \sum_{k \ge 2}T_k$, with all $T_k$ on one probability space as there: by that page $T_{\mathrm{MRCA},n} \uparrow T_\infty$ almost surely, so for $s \ge 0$ the variables $e^{-sT_{\mathrm{MRCA},n}}$ are bounded by $1$ and converge to $e^{-sT_\infty}$ (bounded convergence), and for $-1 < s < 0$ they increase to $e^{-sT_\infty}$ (monotone convergence).

## Depends on

- [Holding times of Kingman's coalescent](../../../Biology/coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)
- [Time to the most recent common ancestor](tmrca.md)
- [Time to the most recent common ancestor of the whole population under Kingman’s coalescent](time-to-the-most-recent-common-ancestor-of-the-w.md)

## Expansion

1. The [holding times](../../../Biology/coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) and their independence.
2. The transform of one exponential variable and the product over independent factors; the domain $s > -1$.
3. Convergence of the infinite product ($\sum_k |s|/(\binom k2 + s) < \infty$) the bounded-convergence step for $s \ge 0$, and the monotone-convergence step for $-1 < s < 0$.
4. Consistency with the [expected TMRCA](../../../Biology/coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md) and the [variance of the TMRCA](../../../Biology/coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/variance-tmrca.md) through the first two derivatives at $s = 0$.

## Sources

- Original result: J. F. C. Kingman, The coalescent, Stochastic Process. Appl. 13 (1982), 235–248. <https://doi.org/10.1016/0304-4149(82)90011-4> The holding times follow Tavaré (2004), Sec. 2.3.
- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188.
