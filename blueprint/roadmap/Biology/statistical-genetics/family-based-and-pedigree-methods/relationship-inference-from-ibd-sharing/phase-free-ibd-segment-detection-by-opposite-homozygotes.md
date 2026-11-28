# Phase-free detection of identity-by-descent segments from opposite homozygotes

Let two diploid samples $s_1, s_2$ be genotyped at biallelic markers coded $0/1$ along a chromosome, partitioned into consecutive windows of $64$ markers. For sample $s$ and window $i$ let $H^{(a)}_{s,i}$ be the set of markers where $s$ is homozygous for allele $a \in \{0,1\}$, and $M_{s,i}$ the set of markers where $s$ is missing. Two samples that share at least one haplotype identically by descent (IBD) at a site carry a common allele there. The only genotype pair with no common allele is opposite homozygotes, since a heterozygote shares an allele with every genotype and missing data is treated as sharing. Hence the set of markers in window $i$ **inconsistent with IBD** is

$$W_i = \big(H^{(0)}_{s_1,i} \cap H^{(1)}_{s_2,i}\big) \cup \big(H^{(1)}_{s_1,i} \cap H^{(0)}_{s_2,i}\big),$$

and the set inconsistent with **IBD2** (both haplotypes shared, hence identical genotypes) is

$$W^{(2)}_i = \big(M_{s_1,i} \cup M_{s_2,i}\big)^{c} \cap \Big(\big(H^{(0)}_{s_1,i} \oplus H^{(0)}_{s_2,i}\big) \cup \big(H^{(1)}_{s_1,i} \oplus H^{(1)}_{s_2,i}\big)\Big),$$

with $\oplus$ the symmetric difference. Neither set requires phased haplotypes.

**IBIS rule.** Putative IBD segments are found sequentially along the chromosome:

1. a segment starts at a window with $W_i = \varnothing$ and is extended window by window while $|W_i| \le 1$ (tolerating genotyping error), tracking the running fraction of mismatching sites across its length;
2. it is terminated as soon as that running fraction exceeds a threshold, at a window with $|W_i| \ge 2$, or at the end of the chromosome, and it ends at the last mismatch-free window ($W_i = \varnothing$);
3. the minimums below are then applied.

The segment is therefore cut at the first point where the running mismatch fraction exceeds the threshold, even if a long clean stretch follows. The source describes the rule this way: "While tracking an ongoing segment, IBIS calculates the fraction of mismatching sites across its length. If this fraction exceeds a user-given threshold, or if the segment reaches the end of the chromosome, the algorithm terminates the segment and chooses the last mismatch-free window as its end point." A segment is kept if its genetic length and marker count exceed minimums (default $7$ cM). IBD2 segments are called similarly from $W^{(2)}_i$ with up to two mismatches per window and a shorter default minimum ($2$ cM), because identical genotypes over a stretch are much stronger evidence. The rest of an IBD region is IBD1.

**Relationship classification.** With $k^{(1)}, k^{(2)}$ the fractions of the genome (in cM) covered by IBD1 and IBD2 segments, the kinship coefficient is estimated as

$$\hat\varphi = \tfrac14 k^{(1)} + \tfrac12 k^{(2)},$$

and a pair is assigned degree $d \ge 1$ when $\hat\varphi \in [2^{-d-3/2}, 2^{-d-1/2})$, using KING's bounds; $\hat\varphi \ge 2^{-3/2}$ indicates duplicates or monozygotic twins. To offset IBD segments shorter than the detection minimum, a constant $0.00138$ (one quarter of the width of KING's sixth-degree interval) is added to $\hat\varphi$.

## Depends on

- [Kinship in the gene-dropping model](../../../quantitative-genetics/gene-dropping-and-identity-by-descent/ibd-model-kinship.md)

## Expansion

Under IBD at a site the two samples' shared haplotype carries the same allele, so a genotype pair $(00, 11)$ or $(11, 00)$ certifies non-IBD up to genotyping error; every other pair is compatible with sharing one haplotype. Long runs free of opposite homozygotes are therefore candidate IBD1-or-IBD2 regions. Unrelated pairs produce such runs only over short distances, at a rate governed by allele frequencies and marker density, which is why a centimorgan minimum is imposed. For IBD2, any homozygote–heterozygote or opposite-homozygote mismatch breaks the identical-genotype requirement; the symmetric differences of the homozygote sets capture exactly the sites where the two genotypes differ (two heterozygotes appear in neither set). Kinship is the probability that random alleles drawn one from each sample are IBD, which equals $\tfrac14$ on IBD1 stretches and $\tfrac12$ on IBD2 stretches, giving $\hat\varphi$. Encoding each window's sets as 64-bit words turns unions, intersections and symmetric differences into bitwise OR, AND and XOR, and $|W_i|$ into a popcount, which makes all-pairs analysis fast.

## Sources

- D. N. Seidman, S. A. Shenoy, M. Kim, R. Babu, I. G. Woods, T. D. Dyer, D. M. Lehman, J. E. Curran, R. Duggirala, J. Blangero and A. L. Williams, "Rapid, phase-free detection of long identity-by-descent segments enables effective relationship classification", The American Journal of Human Genetics 106 (2020), 453–466, Material and methods (Equations 1–2, "Relatedness Classification"), <https://doi.org/10.1016/j.ajhg.2020.02.012> (PMC7118564).
- A. Manichaikul, J. C. Mychaleckyj, S. S. Rich, K. Daly, M. Sale and W.-M. Chen, "Robust relationship inference in genome-wide association studies", Bioinformatics 26 (2010), 2867–2873, <https://doi.org/10.1093/bioinformatics/btq559>.
