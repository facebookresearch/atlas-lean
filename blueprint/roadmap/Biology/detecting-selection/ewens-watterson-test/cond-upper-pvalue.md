# Conditional upper-tail p-value of the Ewens–Watterson test

For a real statistic $T$ of the partitions of $n$ and a partition $\pi$ with $K(\pi)$ parts, the conditional upper-tail p-value is

$$p_T(\pi) = \frac{\sum_{\pi' :\, K(\pi') = K(\pi),\ T(\pi) \le T(\pi')} w(\pi')}{\sum_{\pi' :\, K(\pi') = K(\pi)} w(\pi')},$$

where $w$ is the [cycle-type weight](cycle-type-weight.md). It does not involve $\theta$; by the [sufficiency of $K$](ewens-cond-prob-eq.md) it is the conditional probability, given the observed number of alleles, that $T$ is at least its observed value, for every $\theta > 0$.
