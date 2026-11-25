# Sample allele frequency from genotype counts

A biallelic locus has alleles $A$ and $B$; the genotype class $i \in \{0, 1, 2\}$ of an individual
is its number of copies of $A$. For real genotype counts $n = (n_0, n_1, n_2)$, the sample allele
frequency of $A$ is

$$\hat p(n) = \frac{n_1 + 2 n_2}{2 (n_0 + n_1 + n_2)}.$$

With the convention $x / 0 = 0$, it is $0$ when $n_0 + n_1 + n_2 = 0$, in particular for the empty
table. For nonnegative counts with $n_0 + n_1 + n_2 > 0$ it is the fraction of copies of $A$ among
the $2(n_0 + n_1 + n_2)$ sampled genes, a number in $[0, 1]$.
