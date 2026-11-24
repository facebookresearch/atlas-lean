# Biallelic emission probabilities sum to one

Let $R$ be a field, $\varepsilon \in R$, $k$ a haplotype index and $h$ a column of biallelic reference alleles. Then the [emission weights](emit.md) satisfy

$$\sum_{a \in \{0, 1\}} e_\varepsilon(k, (h, a)) = 1:$$

for each fixed panel column, the emissions sum to one over the target allele.
