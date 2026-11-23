# Exact Hardy–Weinberg p-value

For natural numbers $N$, $n_A$ and $h$, the exact p-value of Wigginton, Cutler and Abecasis is the
total
[Levene probability](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/levene-prob.md)
of the heterozygote counts $j \le n_A$ that are no more probable than $h$:

$$\sum_{j \le n_A,\ L(N, n_A, j) \le L(N, n_A, h)} L(N, n_A, j),$$

the [ordered p-value](ordered-pvalue.md) of $h$ with mass and key both $L(N, n_A, \cdot)$.
