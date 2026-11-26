# Allelic copy-number state space and genotype classes

**Setting.** Before a somatic copy-number change a genomic segment carries one copy of each parental haplotype, and a biallelic SNP in it has germline genotype $AA$, $AB$ or $BB$. After the change the segment has total copy number $h \in \{0, 1, 2, \dots\}$, made of $g$ copies of one parental haplotype and $h - g$ of the other, labelled so that $0 \le g \le h - g$; $g$ is the *minor* and $h - g$ the *major* copy number. The pair $(g, h)$ is the *allelic copy-number state*. A SNP in a segment of state $(g, h)$ has one of the somatic genotypes

$$A^{h}, \qquad A^{h-g}B^{g}, \qquad A^{g}B^{h-g}, \qquad B^{h},$$

the first and last arising from germline homozygotes and the middle two from a germline heterozygote, according to which parental copy carries $B$.

**Proposition.**

1. For fixed total copy number $h$ there are $\lfloor h/2 \rfloor + 1$ states $(g, h)$, and the number of states with $h \le H$ is $\sum_{h=0}^{H} (\lfloor h/2 \rfloor + 1)$.
2. The number of distinct genotype classes in state $(g, h)$ is

$$\begin{cases} 1 & h = 0 \ (\text{homozygous deletion}),\\ 2 & h \ge 1,\ g = 0 \ (\text{loss of heterozygosity}),\\ 3 & g = h/2 \ge 1,\\ 4 & 1 \le g < h/2 . \end{cases}$$

3. A germline heterozygous SNP is observed as heterozygous after the change if and only if $g \ge 1$; loss of heterozygosity ($g = 0$) can occur at any total copy number, including copy-neutral LOH at $h = 2$.

## Expansion

(1) counts $g \in \{0, \dots, \lfloor h/2 \rfloor\}$. (2): the four genotypes coincide pairwise exactly when $g = 0$ ($A^{h-g}B^{g} = A^{h}$ and $A^{g}B^{h-g} = B^{h}$) or $g = h - g$ (the two heterozygous classes coincide), and all collapse to the empty genotype at $h = 0$. (3) is read off the heterozygous classes. For example $h = 3$ allows $(0,3)$ with $\{AAA, BBB\}$ and $(1,3)$ with $\{AAA, AAB, ABB, BBB\}$, while $h = 4$ allows $(0,4)$, $(1,4)$ and $(2,4)$ with $2$, $4$ and $3$ classes. In the source, array intensities are first normalized against germline genotype clusters into a copy-number intensity and a genotype angle, then a Bayesian hidden Markov model over these states (fitted by Baum–Welch, segmented by Viterbi) recovers absolute allelic copy number; this calibrates to non-diploid ploidy, where methods that assume signal proportional to diploid copy number fail because a fixed DNA mass seeds fewer cells of a polyploid tumour.

## Sources

- C. D. Greenman, G. Bignell, A. Butler, S. Edkins, J. Hinton, D. Beare, et al., "PICNIC: an algorithm to predict absolute allelic copy number variation with microarray cancer data", Biostatistics 11 (2010) 164–175, Section 2 and Section 3 with Table 1, <https://doi.org/10.1093/biostatistics/kxp045> (PMC2800165).
