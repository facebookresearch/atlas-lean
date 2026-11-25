# The fitted statistic is N times the squared inbreeding estimate

A biallelic locus has alleles $A$ and $B$; the genotype class $i \in \{0, 1, 2\}$ of an individual
is its number of copies of $A$. Let $n = (n_0, n_1, n_2)$ be nonnegative real genotype counts with
$n_0 + n_1 + n_2 = N$ for a natural number $N$. Then the
[fitted Hardy–Weinberg statistic](hwe-stat.md) is

$$X^2(N, n) = N \hat F(n)^2,$$

where $\hat F$ is the [estimated inbreeding coefficient](inbreeding-hat.md). On a monomorphic table
(all individuals in class $0$, or all in class $2$) and on the empty table both sides are $0$.
