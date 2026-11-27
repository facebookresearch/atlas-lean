# Expected maternal-plasma allelic fraction under fetal inheritance states

Consider a locus at which the mother is heterozygous, with her two alleles assigned (by phasing) to homolog I and homolog II. Maternal plasma contains cell-free DNA with fetal fraction $f \in [0, 1)$: each maternal allele copy contributes with weight proportional to $1 - f$ and each fetal allele copy with weight proportional to $f$. Assume the paternally inherited fetal allele contributes on average half to homolog I and half to homolog II (it matches either maternal allele with equal probability). The fetal **maternal inheritance state** $t$ is $H_1$ or $H_2$ for a euploid fetus (homolog I or II inherited) and $H_{11}$, $H_{22}$ (single-parental-homolog, SPH) or $H_{12}$ (both-parental-homologs, BPH) for a fetus trisomic through a maternal meiotic error. Then the expected fraction $\pi$ of homolog-I alleles among plasma reads is

$$\pi(H_{11}) = \frac{\tfrac52 f + (1 - f)}{3f + 2(1 - f)} = \frac12 + \frac{f}{2 + f}, \qquad \pi(H_1) = \frac{\tfrac32 f + (1 - f)}{2f + 2(1 - f)} = \frac12 + \frac{f}{4},$$

$$\pi(H_{12}) = \frac{\tfrac32 f + (1 - f)}{3f + 2(1 - f)} = \frac12, \qquad \pi(H_2) = \frac12 - \frac f4, \qquad \pi(H_{22}) = \frac12 - \frac{f}{2 + f}.$$

## Depends on

- [Inheritance Vector](../inheritance-vector.md): the maternal inheritance state records which maternal homolog was transmitted
- [Mendel's law of segregation](../../../population-genetics/hardy-weinberg-law/transmit.md): transmission of one parental homolog per meiosis

## Expansion

The denominator counts allele copies weighted by source: two maternal copies, and two (euploid) or three (trisomic) fetal copies. The numerator counts homolog-I copies: one from the mother, the maternally inherited fetal copies of homolog I ($1$ for $H_1$, $2$ for $H_{11}$, $1$ for $H_{12}$, $0$ for $H_2$, $H_{22}$) and half a copy from the paternal allele. SPH segments shift the allelic fraction by about $f/2$, twice the euploid shift $f/4$, while BPH segments show no shift at all; a trisomy is therefore visible only through SPH segments, and an unphased analysis must detect a deviation of the pooled distribution, whereas with phase the direction of the deviation is known at each site. In a trisomy, crossovers in the erroneous meiosis switch the state between SPH and BPH along the chromosome; phasing errors swap $H_1 \leftrightarrow H_2$ and $H_{11} \leftrightarrow H_{22}$.

## Sources

- G. Genovese, C. J. Mello, P.-R. Loh, R. E. Handsaker, S. Kashin, C. W. Whelan, L. A. Bayer-Zwirello and S. A. McCarroll, "Chromosomal phase improves aneuploidy detection in non-invasive prenatal testing at low fetal DNA fractions", *Scientific Reports* 12 (2022), 12025, Methods "NIPT simulation", <https://doi.org/10.1038/s41598-022-14049-5> (PMC9283487).
