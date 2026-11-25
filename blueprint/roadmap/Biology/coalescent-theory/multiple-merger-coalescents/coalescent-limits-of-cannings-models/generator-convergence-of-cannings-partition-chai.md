# Generator convergence of Cannings ancestral partition chains under pattern limits

Fix $n \ge 2$. For a sequence of [Cannings models](../cannings-models/cannings-model.md) indexed by the population size $N$, let $c_N$ be the probability that two sampled children share a parent, and let $P_N(\pi)$ be the [one-generation probability](../cannings-models/exact-one-generation-sampling-identity-for-canni.md) that $b$ sampled children are grouped by common parent according to the partition $\pi$ of $[b]$.

Assume the pattern-limit hypothesis: $c_N > 0$ for all large $N$, $c_N \to 0$, and for every $b \le n$ and every partition $\pi$ of $[b]$ other than the partition into singletons, the finite limit

$$q(\pi) = \lim_{N \to \infty} \frac{P_N(\pi)}{c_N}$$

exists. Order the blocks of a partition $\xi$ of $[n]$ with $b$ blocks by their least elements. For $\xi' \ne \xi$, set $Q_n(\xi, \xi') = q(\pi)$ when $\xi'$ is obtained from $\xi$ by merging its blocks according to a non-singleton partition $\pi$ of $[b]$, and $0$ otherwise. Set $Q_n(\xi, \xi) = -\sum_{\pi} q(\pi)$, the sum over the non-singleton partitions $\pi$ of $[b]$.

Then $Q_n$ is a rate matrix on the partitions of $[n]$, and the one-generation transition matrix $\Pi_N$ of the ancestral partition chain satisfies

$$\frac{1}{c_N} (\Pi_N - I) \to Q_n \qquad \text{entrywise}.$$

## Depends on

- [One-generation sampling identity for Cannings partitions](../cannings-models/exact-one-generation-sampling-identity-for-canni.md)
- [Cannings model of a haploid population](../cannings-models/cannings-model.md)

## Expansion

1. Off-diagonal entries converge by the hypothesis. The diagonal converges because $1 - \Pi_N(\xi, \xi) = \sum_{\pi} P_N(\pi)$ over the non-singleton $\pi$.
2. The rows of $Q_n$ sum to $0$ and its off-diagonal entries are nonnegative.
3. For the sweepstake model (with probability $c_N$ all children share one uniform parent, otherwise parents are a uniform bijection), $q(\{1,2\}\{3\}) = 0$ and $q(\{1,2,3\}) = 1$: the rates of the Λ-coalescent with $\Lambda = \delta_1$, for which $\lambda_{3,2} = 0$.

## Sources

- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, *Ann. Probab.* 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761> (generator limit).
