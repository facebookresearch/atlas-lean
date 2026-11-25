# Estimated inbreeding coefficient

A biallelic locus has alleles $A$ and $B$; the genotype class $i \in \{0, 1, 2\}$ of an individual
is its number of copies of $A$. For real genotype counts $n = (n_0, n_1, n_2)$, the estimated
inbreeding coefficient is

$$\hat F(n) = \frac{4 n_0 n_2 - n_1^2}{(2 n_0 + n_1)(n_1 + 2 n_2)}.$$

With the convention $x / 0 = 0$, it is $0$ when $2 n_0 + n_1 = 0$ or $n_1 + 2 n_2 = 0$; for
nonnegative counts these are the monomorphic tables, in which no copy of $B$, respectively of $A$,
was sampled, and the empty table. When both sums and $n_0 + n_1 + n_2$ are nonzero it equals
[one minus the observed over the expected heterozygosity](inbreeding-hat-eq-one-sub.md).
