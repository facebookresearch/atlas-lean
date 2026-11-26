# Ratio of averages versus average of ratios for genome-wide $F_{ST}$

Let SNPs $s = 1, \dots, L$ each have a single-SNP $F_{ST}$ written as a ratio $\hat F_s = N_s / D_s$ of a numerator and a positive denominator (for example Hudson's), and assume the pairs $(N_s, D_s)$ are independent and identically distributed with $\mathbb E|N_s| < \infty$, $\mathbb E[D_s] = \delta \in (0, \infty)$ and $\mathbb E|N_s / D_s| < \infty$; write $\nu = \mathbb E[N_s]$. Two genome-wide summaries are in use:

$$\hat F_{\mathrm{RoA}} = \frac{\sum_{s=1}^L N_s}{\sum_{s=1}^L D_s}, \qquad \hat F_{\mathrm{AoR}} = \frac{1}{L}\sum_{s=1}^L \frac{N_s}{D_s}.$$

As $L \to \infty$, $\hat F_{\mathrm{RoA}} \to \nu/\delta$ almost surely, so the ratio of averages is consistent for the population parameter $\nu/\delta$ whenever $N_s$ and $D_s$ are unbiased for the between-population and total variance components. The average of ratios converges almost surely instead to $\mathbb E[N_s/D_s]$, which in general differs from $\nu/\delta$. Independence with common first moments alone would not suffice: with $D_s = 1$ and independent $N_s$ equal to $s^2$ with probability $s^{-2}$ and $0$ otherwise, every $N_s$ has mean $1$, yet by the Borel–Cantelli lemma only finitely many are nonzero, so $\hat F_{\mathrm{RoA}} \to 0$ almost surely. In particular, a population-private rare variant with frequencies $p_1 = \varepsilon$, $p_2 = 0$ has Hudson numerator $\varepsilon^2$ and denominator $\varepsilon$, hence single-SNP value $\varepsilon \to 0$; adding many such SNPs drives $\hat F_{\mathrm{AoR}}$ toward zero while barely moving $\hat F_{\mathrm{RoA}}$.

## Depends on

- [Hudson's $F_{ST}$ (ratio of averages)](../abba-baba-test-and-f-statistic-estimators/hudson-fst.md)

## Expansion

The strong law of large numbers for i.i.d. integrable variables, applied separately to $L^{-1}\sum N_s$ and $L^{-1}\sum D_s$, followed by continuity of $(x,y) \mapsto x/y$ at $(\nu,\delta)$, gives consistency of the ratio of averages, and the same law applied to the integrable ratios $N_s/D_s$ gives the limit of the average of ratios, although no unbiased estimator of the ratio itself is known. The average of ratios weights every SNP equally regardless of its informativeness, so low-frequency SNPs, whose single-SNP values are small, dominate when sequencing discovers many of them; the bias therefore grows with sample size and sequencing depth. Bhatia et al. found that for CEU versus CHB in 1000 Genomes data the ratio of averages gives 0.106 and the average of ratios 0.072, and that the average of ratios combined with ascertainment of SNPs polymorphic in either population gives 0.047, close to the much lower published estimate that motivated their analysis.

## Sources

- G. Bhatia, N. Patterson, S. Sankararaman, A. L. Price, "Estimating and interpreting $F_{ST}$: the impact of rare variants", Genome Research 23 (2013), 1514–1521, <https://doi.org/10.1101/gr.154831.113> (PMC3759727), Results "Combining estimates of $F_{ST}$ across multiple SNPs" and Methods.
- B. S. Weir and C. C. Cockerham, "Estimating F-statistics for the analysis of population structure", Evolution 38 (1984), 1358–1370, <https://doi.org/10.1111/j.1558-5646.1984.tb05657.x>.
