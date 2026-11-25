# Pooled genotype-score variance

For a [case-control genotype table](total.md) $r, s$ with total $N$ and pooled counts $n_i = r_i + s_i$, the pooled genotype-score variance is

$$\mathrm{Var} = \frac{1}{N} \sum_{i=0}^{2} i^2 n_i - \Bigl(\frac{1}{N} \sum_{i=0}^{2} i\, n_i\Bigr)^2,$$

with the convention $x/0 = 0$. When the counts are nonnegative and $N > 0$, it is the empirical variance of the genotype score (the number of counted alleles) over the $N$ individuals.
