# Pooled allele frequency

For a [case-control genotype table](total.md) $r, s$ with total $N$ and pooled counts $n_i = r_i + s_i$, the pooled frequency of the counted allele is

$$p = \frac{\sum_{i=0}^{2} i\, n_i}{2N},$$

with the convention $x/0 = 0$. When the counts are nonnegative and $N > 0$, it is the frequency of the counted allele among the $2N$ genes of the table.
