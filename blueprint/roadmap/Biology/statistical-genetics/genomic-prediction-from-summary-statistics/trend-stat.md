# Cochran–Armitage trend statistic

For a [case-control genotype table](total.md) $r, s$ with total $N$, $R = \sum_i r_i$ cases, $S = \sum_i s_i$ controls, pooled counts $n_i = r_i + s_i$ and [trend numerator](numer.md) $U$, the Cochran–Armitage trend statistic with scores $0, 1, 2$ is (Armitage 1955)

$$T = \frac{N U^2}{R S \bigl(N \sum_i i^2 n_i - (\sum_i i\, n_i)^2\bigr)},$$

with the convention $x/0 = 0$.

## Sources

- P. Armitage, *Tests for linear trends in proportions and frequencies*, Biometrics 11 (1955), 375–386.
