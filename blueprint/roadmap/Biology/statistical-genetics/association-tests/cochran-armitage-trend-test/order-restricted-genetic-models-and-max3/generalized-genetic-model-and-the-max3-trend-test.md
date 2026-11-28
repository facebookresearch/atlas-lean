# Generalized genetic model and the MAX3 trend test

**Data and risks.** A diallelic SNP with alleles $A, a$ in a case-control study gives a $2\times 3$ table: $r_1, r_2, r_3$ cases and $s_1, s_2, s_3$ controls with genotypes $AA, Aa, aa$; $r = \sum r_i$, $s = \sum s_i$, $n_i = r_i + s_i$, $n = r + s$. Cases and controls are trinomial, $\mathrm{TN}(r; p_1,p_2,p_3)$ and $\mathrm{TN}(s; q_1,q_2,q_3)$. The genotype relative risks are

$$\Lambda_1 = \frac{\mathbb{P}(\text{case}\mid Aa)}{\mathbb{P}(\text{case}\mid AA)},\qquad \Lambda_2 = \frac{\mathbb{P}(\text{case}\mid aa)}{\mathbb{P}(\text{case}\mid AA)}.$$

No association means $\Lambda_1 = \Lambda_2 = 1$, equivalently $p_i = q_i$ for all $i$.

**Generalized genetic model (order-restricted relative risks).** If $a$ is the disease allele, the alternative is $1 \le \Lambda_1 \le \Lambda_2$ with at least one inequality strict; if $A$ is the disease allele, $1 \ge \Lambda_1 \ge \Lambda_2$ with at least one strict. The classical models are special cases: recessive ($\Lambda_1 = 1 < \Lambda_2$), additive ($\Lambda_1 = (1+\Lambda_2)/2$) and dominant ($\Lambda_1 = \Lambda_2 > 1$).

**Trend tests and MAX3.** For scores $(0, x, 1)$ assigned to $(AA, Aa, aa)$, the Cochran-Armitage trend statistic is

$$Z_x = \frac{\sqrt{n}\,\sum_{i} w_i\,(s\,r_i - r\,s_i)}{\sqrt{r\,s\,\big[n\sum_i w_i^2 n_i - (\sum_i w_i n_i)^2\big]}},\qquad (w_1,w_2,w_3) = (0,x,1).$$

It is asymptotically $N(0,1)$ under the null and is the locally optimal test when $x$ matches the true model: $x = 0$ recessive, $x = 1/2$ additive, $x = 1$ dominant. When the model is unknown, the robust statistic $\mathrm{MAX3} = \max\{|Z_0|, |Z_{1/2}|, |Z_1|\}$ is used; its null distribution follows from the asymptotic joint normality of $(Z_0, Z_{1/2}, Z_1)$.

## Depends on

- [Trend statistic of a case-control table](../../../genomic-prediction-from-summary-statistics/trend-stat.md)

## Expansion

Under the generalized genetic model, trend statistics with every score $x\in[0,1]$ have means of one sign, set by which allele is the risk allele, so testing over the family of models in the order-restricted cone gives more power than a single fixed-score test, which loses power far from its own model. Chen (2014, Theorem 1) shows that the standardized contrasts used by the allele-selection test are asymptotically multivariate normal with a singular covariance (one is a linear combination of the other two). That test chooses the disease allele by the sign of one contrast, then combines the two one-sided p-values for that allele through $\chi^2_1$ quantiles, with the null distribution obtained by simulating from the fitted Gaussian. In simulations it matched MAX3 and genetic model selection near additive models and was more powerful under dominant and over-dominant models.

## Sources

- Chen Z. A new association test based on disease allele selection for case-control genome-wide association studies. *BMC Genomics* 15:358 (2014), Methods, Eqs. 1-3 and Theorem 1. <https://doi.org/10.1186/1471-2164-15-358>. PMCID: PMC4059871.
- Freidlin B, Zheng G, Li Z, Gastwirth JL. Trend tests for case-control studies of genetic markers: power, sample size and robustness. *Human Heredity* 53:146-152 (2002).
