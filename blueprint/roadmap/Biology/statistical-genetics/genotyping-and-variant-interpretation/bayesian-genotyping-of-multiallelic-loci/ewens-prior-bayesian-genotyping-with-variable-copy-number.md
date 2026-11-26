# Ewens-prior Bayesian genotyping with variable copy number

With the notation of the [genotype-combination sampling probability](unphased-genotype-combination-sampling-probability.md), let $R_i$ be the reads of sample $i$, which yield observed alleles $b'_1,\dots,b'_{k_i}$ with counts $o'_1,\dots,o'_{k_i}$ ($\sum_jo'_j=s_i$) and per-observation error probabilities $q_l$. The posterior over joint genotypings is

$$P(G_1,\dots,G_n\mid R_1,\dots,R_n)=\frac{P(G_1,\dots,G_n)\prod_{i=1}^nP(R_i\mid G_i)}{\sum_{G'_1,\dots,G'_n}P(G'_1,\dots,G'_n)\prod_{i=1}^nP(R_i\mid G'_i)},$$

with the following components.

- Data likelihood: sampling observations with replacement from $G_i$ is multinomial, $P(R_i\mid G_i)\approx\frac{s_i!}{\prod_jo'_j!}\prod_j\big(f_{ij}/m_i\big)^{o'_j}$, refined by summing over the true-allele assignments compatible with $G_i$ and multiplying by $\prod_lP(b'_l\mid b_l)$, where $P(b'_l\mid b_l)=1-q_l$ if $b_l\in G_i$ and $q_l$ otherwise.
- Prior: $P(G_1,\dots,G_n)=P(G_1,\dots,G_n\mid f_1,\dots,f_K)\,P(f_1,\dots,f_K)$, since the allele counts are a function of the genotypes.
- Frequency prior: if $a_j$ alleles have sample count $j$ ($\sum_jja_j=M$), then under a neutral infinite-alleles equilibrium with population mutation rate $\theta$,

$$P(f_1,\dots,f_K)=P(a_1,\dots,a_M)=\frac{M!}{\theta(\theta+1)\cdots(\theta+M-1)}\prod_{j=1}^M\frac{\theta^{a_j}}{j^{a_j}a_j!}.$$

The probability that the locus is polymorphic is $P(K>1\mid R)=1-P(K=1\mid R)$, and the marginal posterior of one sample's genotype is the sum of joint posteriors over genotypings containing it.

## Depends on

- [Sampling probability of an unphased genotype combination](unphased-genotype-combination-sampling-probability.md)
- [Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)
## Expansion

The prior couples samples, so the posterior pools information across individuals, unlike per-sample maximum likelihood. In the biallelic case the Ewens term is $\frac{M!}{\prod_{z=1}^{M-1}(\theta+z)}\frac{\theta}{f_1f_2}$, and in the monomorphic case $\frac{(M-1)!}{\prod_{z=1}^{M-1}(\theta+z)}$, which for $M=2$ equals $1/(1+\theta)\approx1-\theta$ for small $\theta$. Because exhaustive summation is infeasible, the posterior mode is found by local search starting from per-sample maximum-likelihood genotypes, changing one sample at a time among its top few genotypes.

## Sources

- E. Garrison, G. Marth, "Haplotype-based variant detection from short-read sequencing", arXiv:1207.3907 (2012), Sections 2.2–2.4 and 3.3–3.5, Equations (2)–(6), (10)–(12), (15)–(16), <https://doi.org/10.48550/arXiv.1207.3907>.
