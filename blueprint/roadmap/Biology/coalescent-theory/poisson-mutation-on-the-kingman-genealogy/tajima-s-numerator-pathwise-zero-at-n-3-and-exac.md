# Tajima's numerator vanishes identically for three genes

For a sample of $n = 3$ genes at infinitely many sites, every segregating site has derived-allele count $i \in \{1, 2\}$, and contributes
$i(3 - i)/\binom32 = \frac23$ to the mean number of pairwise differences $\pi$. With $S$ segregating sites, $\pi = \frac23 S$, while $a_1 = 1 + \frac12 = \frac32$, so

$$\pi - \frac{S}{a_1} = \frac23 S - \frac23 S = 0$$

for every sample, whatever the demography or selection. The numerator of [Tajima's D](../../detecting-selection/tajima-s-d/tajima-d.md) is identically zero for $n = 3$. Its denominator vanishes too: $b_1 = \frac23 = \frac1{a_1}$ and
$b_2 = \frac59$, $\frac{n + 2}{a_1 n} = \frac{10}9$, $\frac{a_2}{a_1^2} = \frac59$, so $c_1 = c_2 = 0$ and $e_1 = e_2 = 0$. So $D$ carries no information for three genes
(it is $0$ only by the division convention of its definition), and three genes cannot detect departures from neutrality or
constant size through $D$.

## Depends on

- [Tajima's D](../../detecting-selection/tajima-s-d/tajima-d.md)

## Expansion

For $n = 4$, under a time-changed Kingman coalescent, $\mathbb E[\pi - S/a_1] = (\theta/2)\bigl(\frac{2}{99}\mathbb E T_2 + \frac{1}{33}\mathbb E T_3 - \frac{2}{11}\mathbb E T_4\bigr)$, which vanishes for constant size;
it needs the law of the ranked topology given the epoch lengths and is a separate statement.

## Sources

- F. Tajima, "Statistical method for testing the neutral mutation hypothesis by DNA polymorphism", Genetics 123 (1989), 585–595, <https://doi.org/10.1093/genetics/123.3.585>. The identity is derived above.
