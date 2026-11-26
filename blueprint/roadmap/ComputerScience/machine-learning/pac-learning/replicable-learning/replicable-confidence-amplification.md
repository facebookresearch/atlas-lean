# Confidence amplification of replicable algorithms by majority and median

Let $A$ be $\rho$-replicable over $\mathcal{D}$ and run it $2(r+1)$ times on disjoint blocks of samples with independent shared seeds.

1. For Boolean outputs, the majority vote (ties to true) is $2(r+1)\rho$-replicable; if $A$ outputs a target bit $\tau(D)$ except with probability $\beta_0 \le 1/2$, the majority errs with probability at most $(4\beta_0(1-\beta_0))^{r+1}$.
2. For real outputs, the median of the runs is $2(r+1)\rho$-replicable; if $A$ is an $(\varepsilon, \beta_0)$-estimator with $\beta_0 < 1/2$, then for every $\beta > 0$ some $r$ makes the median an $(\varepsilon, \beta)$-estimator.

## Proof sketch

Replicability follows from block composition and post-processing. The majority errs only if at least $r+1$ of $2(r+1)$ independent runs err, which has probability at most $\sum_{j \ge r+1}\binom{2(r+1)}{j}\beta_0^{j}(1-\beta_0)^{2(r+1)-j} \le 2^{2(r+1)}\beta_0^{r+1}(1-\beta_0)^{r+1} = (4\beta_0(1-\beta_0))^{r+1}$, since $\beta_0 \le 1/2$ gives $\beta_0^{j}(1-\beta_0)^{2(r+1)-j} \le \beta_0^{r+1}(1-\beta_0)^{r+1}$ for $j \ge r+1$; the median lies in the target interval whenever a strict majority of runs do.

## Depends on

- [Composition of replicable algorithms](composition-of-replicable-algorithms.md)
- [Median amplification](../../../../Probability/concentration-inequalities/median-of-means-amplification/measure-real-sample-median-not-mem-icc-l.md)

## Proof depends on

- [Composition of replicable algorithms](composition-of-replicable-algorithms.md)
- [Median amplification](../../../../Probability/concentration-inequalities/median-of-means-amplification/measure-real-sample-median-not-mem-icc-l.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
