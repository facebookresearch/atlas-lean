# Exact p-value for a heterozygote deficit

For natural numbers $N$, $n_A$ and $h$, the one-sided exact p-value for a heterozygote deficit is

$$\sum_{j \le \min(h, n_A)} L(N, n_A, j),$$

the sum of the
[Levene probabilities](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/levene-prob.md)
$L(N, n_A, j)$ of the heterozygote counts $j \le n_A$ with $j \le h$: the
[ordered p-value](ordered-pvalue.md) with key $g(j) = j$. When $n_A \le 2N$,
[Levene's law](levene-measure.md) is a probability measure and the p-value is the probability under
it of at most $h$ heterozygotes. When $n_A > 2N$ every Levene probability is $0$, so there is no
such law, and the p-value is $0$ for every $h$ (for example $N = 0$, $n_A = 1$).
