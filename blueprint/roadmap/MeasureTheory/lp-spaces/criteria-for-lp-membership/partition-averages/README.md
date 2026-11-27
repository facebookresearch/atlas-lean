# L^p on [0, 1] via averages over partitions

Let $f$ be in $L^1([0, 1])$ and let $p > 1$. Then $f \in L^p([0, 1])$ if and only if the partition
sums

$$\sum_{i=0}^{n-1} (t_{i+1} - t_i) \left( \frac{1}{t_{i+1} - t_i} \int_{t_i}^{t_{i+1}} |f(x)|\, dx \right)^p$$

are bounded over all partitions $0 = t_0 < t_1 < \dots < t_n = 1$ of $[0, 1]$.

## Idea

The criterion replaces the integral of $|f|^p$ by sums of averages, which are easier to bound.
Jensen's inequality bounds each term by $\int_{t_i}^{t_{i+1}} |f|^p$, which gives one direction.
Conversely, along finer and finer dyadic partitions the averages converge to $|f|$ almost
everywhere, by Lebesgue's differentiation theorem, and Fatou's lemma bounds $\int |f|^p$ by the
supremum of the sums.

## Statements

- [$L^p$ on $[0,1]$ via averages over partitions](mem-lp-iff-bdd-above-partition-average-s.md)
- [Partition average sum](partition-average-sum.md): the sums of the statement.
- [Partitions of the unit interval](is-partition01.md): the partitions of the statement.
