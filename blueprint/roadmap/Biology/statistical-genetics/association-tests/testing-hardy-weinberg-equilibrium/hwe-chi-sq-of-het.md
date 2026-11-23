# Hardy–Weinberg statistic as a function of the heterozygote count

For natural numbers $N$, $n_A$ and $h$, the statistic is the
[fitted Hardy–Weinberg statistic](hwe-stat.md) $X^2(N, n)$ of the genotype table
$n = (n_{BB}, n_{AB}, n_{AA})$ with

$$
n_{BB} = \Bigl\lfloor \frac{2N \mathbin{\dot{-}} n_A \mathbin{\dot{-}} h}{2} \Bigr\rfloor, \qquad
n_{AB} = h, \qquad n_{AA} = \Bigl\lfloor \frac{n_A \mathbin{\dot{-}} h}{2} \Bigr\rfloor,
$$

whose class $i$ counts the individuals carrying $i$ copies of $A$; here $\lfloor \cdot \rfloor$ is
the floor of natural-number division and $a \mathbin{\dot{-}} b = \max(a - b, 0)$ is truncated
subtraction. On a realizable count ($h \le n_A$, $h + n_A \le 2N$, $n_A - h$ even) the table is the
exact genotype table. On the other counts it is not: for example for $h > n_A$ the $AA$ entry is
$0$. Those counts have
[Levene probability](../../../../Probability/hypothesis-testing/exact-test-for-hardy-weinberg-equilibrium/levene-prob.md)
$0$.
