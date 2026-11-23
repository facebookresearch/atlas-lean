# Exact p-value for a heterozygote deficit

For natural numbers $N$, $n_A$ and $h$, the one-sided exact p-value for a heterozygote deficit is

$$\sum_{j \le \min(h, n_A)} L(N, n_A, j),$$

the total
[Levene probability](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/levene-prob.md)
of the heterozygote counts $j \le n_A$ with $j \le h$: the [ordered p-value](ordered-pvalue.md) with
key $g(j) = j$. When $n_A \le 2N$ it is the probability of at most $h$ heterozygotes under
[Levene's law](levene-measure.md).
