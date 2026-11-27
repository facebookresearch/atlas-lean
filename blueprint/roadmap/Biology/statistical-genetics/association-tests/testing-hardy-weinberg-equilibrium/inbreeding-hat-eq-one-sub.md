# Inbreeding estimate: one minus observed over expected heterozygosity

A biallelic locus has alleles $A$ and $B$; the genotype class $i \in \{0, 1, 2\}$ of an individual
is its number of copies of $A$. Let $n = (n_0, n_1, n_2)$ be real genotype counts with
$2 n_0 + n_1 \ne 0$, $n_1 + 2 n_2 \ne 0$ and $n_0 + n_1 + n_2 \ne 0$; for nonnegative counts these
say that both alleles were sampled. Then the [estimated inbreeding coefficient](inbreeding-hat.md)
is

$$
\hat F(n) = 1 - \frac{H_{\mathrm{obs}}}{H_{\mathrm{exp}}}, \qquad
H_{\mathrm{obs}} = \frac{n_1}{n_0 + n_1 + n_2}, \quad H_{\mathrm{exp}} = 2 \hat p (1 - \hat p),
$$

the observed heterozygosity over the heterozygosity expected under Hardy–Weinberg proportions at the
[sample allele frequency](allele-freq-hat.md) $\hat p$.
