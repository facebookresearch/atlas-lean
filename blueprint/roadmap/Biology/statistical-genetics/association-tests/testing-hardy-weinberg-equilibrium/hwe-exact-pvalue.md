# Exact Hardy–Weinberg p-value

For natural numbers $N$, $n_A$ and $h$, the exact p-value of Wigginton, Cutler and Abecasis is

$$\sum_{j \le n_A,\ L(N, n_A, j) \le L(N, n_A, h)} L(N, n_A, j),$$

the sum of the
[Levene probabilities](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/levene-prob.md)
$L(N, n_A, j)$ of the heterozygote counts $j \le n_A$ that are no more probable than $h$: the
[ordered p-value](ordered-pvalue.md) of $h$ with mass and key both $L(N, n_A, \cdot)$. When
$n_A \le 2N$, [Levene's law](levene-measure.md) is a probability measure and the p-value is the
probability under it of a heterozygote count no more probable than $h$. When $n_A > 2N$ every Levene
probability is $0$, so there is no such law, and the p-value is $0$ for every $h$ (for example
$N = 0$, $n_A = 1$).
