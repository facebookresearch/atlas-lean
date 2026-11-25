# DENTIST-S statistic

For real numbers $r$ (the reference correlation between a variant and the lead variant), $z_i$ (the $z$-score of the variant) and $z_c$ (the $z$-score of the lead, putatively causal, variant), the DENTIST-S statistic is (Kanai et al. 2022, Equation 1)

$$T = \frac{(z_i - r z_c)^2}{1 - r^2},$$

with the convention $x/0 = 0$ (so $T = 0$ when $r^2 = 1$); it is meaningful for $r^2 < 1$.

## Sources

- M. Kanai, R. Elzur, W. Zhou, Global Biobank Meta-analysis Initiative, M. J. Daly, H. K. Finucane, *Meta-analysis fine-mapping is often miscalibrated at single-variant resolution*, Cell Genomics 2 (2022), 100210, Equation 1.
