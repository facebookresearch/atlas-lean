# The time-t marginal of the partition-valued coalescent

For every natural number $n$, every real $t$ and every partition $\pi \in \mathcal{P}_n$,

$$e^{t Q_n}(\bot, \pi) = e^{t G_n}(n, |\pi|)\; p_n(\pi),$$

where $Q_n$ is the [partition rate matrix](partition-rate.md), $G_n$ the [generator of Kingman's block-counting process](../ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md) and $p_n$ [Kingman's formula](kingman-prob.md). For $t \ge 0$: the probability of a partition with $k$ blocks at time $t$ is the probability that the block-counting process goes from $n$ to $k$ lineages in time $t$, times Kingman's formula.

## Sources

- J. F. C. Kingman, *The coalescent*, Stochastic Process. Appl. 13 (1982), 235–248.
