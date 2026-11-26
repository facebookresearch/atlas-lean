# Genetic distance between cases and controls of two disorders

Let disorders $A$ and $B$ have lifetime prevalences $K_A, K_B$, observed-scale SNP heritabilities $h^2_{oA}, h^2_{oB}$ (for 50/50 case–control ascertainment) and genetic correlation $r_g$, with coheritability $c_{AB} = r_g\,h_{oA}h_{oB}$, all measured on $m$ independent SNPs whose effects on the two disorders follow a bivariate normal distribution. Write $\beta_A, \beta_B$ for a SNP's standardized case–control effects, with $\operatorname{var}\beta_A = h^2_{oA}/m$, $\operatorname{var}\beta_B = h^2_{oB}/m$, $\operatorname{cov}(\beta_A,\beta_B) = c_{AB}/m$.

**Group offsets.** Relative to the population mean, the standardized allele-frequency offsets of the four groups are $(1-K_A)\beta_A$ for cases of $A$ ($A1$), $-K_A\beta_A$ for controls of $A$ ($A0$), and $(1-K_B)\beta_B$, $-K_B\beta_B$ for $B1$, $B0$.

**Distances.** The average normalized squared allele-frequency difference at causal SNPs, $F_{ST,\mathrm{causal}}$, between two groups is the variance of the difference of their offsets:

$$F_{A1A0} \approx \frac{h^2_{oA}}{m}, \qquad F_{B1B0} \approx \frac{h^2_{oB}}{m},$$

$$F_{A1B1} \approx \frac{h^2_{oA}(1-K_A)^2 - 2c_{AB}(1-K_A)(1-K_B) + h^2_{oB}(1-K_B)^2}{m},$$

$$F_{A1B0} \approx \frac{h^2_{oA}(1-K_A)^2 + 2c_{AB}(1-K_A)K_B + h^2_{oB}K_B^2}{m},$$

$$F_{A0B1} \approx \frac{h^2_{oA}K_A^2 + 2c_{AB}K_A(1-K_B) + h^2_{oB}(1-K_B)^2}{m},$$

$$F_{A0B0} \approx \frac{h^2_{oA}K_A^2 - 2c_{AB}K_AK_B + h^2_{oB}K_B^2}{m}.$$

The quantities $\sqrt{m\,F}$ do not depend on $m$ and are Euclidean distances among the four groups in a plane, in which $r_g$ is the cosine of the angle between the segments from the population mean to $A1$ and to $B1$.

## Depends on

- [Case–case allele-frequency identity and the CC-GWAS estimators](case-case-allele-frequency-identity-and-cc-gwas-estimators.md)

## Expansion

Each offset follows from $p_{A1} - p = (1-K_A)(p_{A1}-p_{A0})$ and $p_{A0} - p = -K_A(p_{A1}-p_{A0})$; the variance of a linear combination $x\beta_A + y\beta_B$ is $(x^2h^2_{oA} + 2xy\,c_{AB} + y^2h^2_{oB})/m$. The offsets $(1-K_A)\beta_A$ and $(1-K_B)\beta_B$ have covariance proportional to $r_g$ times the product of their standard deviations, which gives the angle interpretation. Unlike population-genetic $F_{ST}$ (about $0.11$ between European and East Asian samples), $F_{ST,\mathrm{causal}}$ between cases and controls is of order $10^{-6}$; $\sqrt{mF}$ is proportional to average GWAS power and to polygenic prediction accuracy for the comparison.

## Sources

- W. J. Peyrot, A. L. Price, "Identifying loci with different allele frequencies among cases of eight psychiatric disorders using CC-GWAS", Nature Genetics (2021), Methods ("Quantifying genetic distances between cases and/or controls of each disorder"), <https://doi.org/10.1038/s41588-021-00787-1>.
