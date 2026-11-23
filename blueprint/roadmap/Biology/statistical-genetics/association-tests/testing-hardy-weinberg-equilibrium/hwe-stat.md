# Pearson's Hardy–Weinberg statistic with estimated allele frequency

A biallelic locus has alleles $A$ and $B$; the genotype class $i \in \{0, 1, 2\}$ of an individual
is its number of copies of $A$. For a natural number $N$ and real genotype counts
$n = (n_0, n_1, n_2)$, the statistic is Pearson's statistic of $n$ against the
[Hardy–Weinberg proportions](hwe-prob.md) $\pi(p) = ((1 - p)^2, 2p(1 - p), p^2)$ at the
[sample allele frequency](allele-freq-hat.md) $\hat p$ of $n$:

$$X^2(N, n) = \sum_{i = 0}^{2} \frac{\bigl(n_i - N \pi_i(\hat p)\bigr)^2}{N \pi_i(\hat p)}.$$

With the convention $x / 0 = 0$, a class with $N \pi_i(\hat p) = 0$ contributes $0$; this happens
for every class when $N = 0$, and for the heterozygote class and one homozygote class when $\hat p$
is $0$ or $1$. The sample size $N$ is an argument of its own: the intended use is with
$N = n_0 + n_1 + n_2$.
