# Empirical quartet frequencies eventually recover the species quartets

Let gene trees $G_1, G_2, \dots$ be independent draws from the multispecies coalescent on an unrooted binary species tree $S$ with one lineage
per taxon. Assume that, for every four-taxon set $q$, the resolution $\rho_q$ induced by $S$ has probability $1 - \frac23 e^{-t_q}$, and each of the two other
resolutions has probability $\frac13 e^{-t_q}$, where $t_q > 0$ is the internal length of the induced quartet; this is the four-taxon analogue of [three-species concordance](../../coalescent-theory/multispecies-coalescent/gene-tree-prob-triple-matching.md).
Then $\rho_q$ beats each alternative by $1 - e^{-t_q} > 0$. Since there are finitely many four-taxon sets, the [strong law of large numbers](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md) applied to
the indicator of each resolution (the gene trees are independent and identically distributed) shows that, almost surely, for all large $n$ the empirical resolution frequencies among $G_1, \dots, G_n$ form a
[strict plurality](is-strict-plurality.md) for $S$. No majority claim is made: at $t_q = 0.1$ the induced resolution has probability $0.39678$ against $0.30161$ for each
alternative. At $t_q = 0$ the margin is $0$, which the hypothesis excludes.

## Depends on

- [Strict plurality of the induced resolutions](is-strict-plurality.md)

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Sources

- E. S. Allman, J. H. Degnan and J. A. Rhodes, "Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent", Journal of Mathematical Biology 62 (2011), 833–862, <https://doi.org/10.1007/s00285-010-0355-7> (unrooted quartet probabilities).
