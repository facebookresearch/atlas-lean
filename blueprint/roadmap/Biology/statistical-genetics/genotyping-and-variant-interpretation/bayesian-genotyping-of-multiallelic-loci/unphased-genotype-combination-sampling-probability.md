# Sampling probability of an unphased genotype combination

Let $n$ samples have copy numbers $m_1,\dots,m_n\ge1$ at a locus, with $M=\sum_i m_i$ gene copies in total. Suppose the $M$ copies carry $K$ distinct alleles with sample counts $f_1,\dots,f_K$, $\sum_l f_l=M$. An unphased genotype $G_i$ of sample $i$ is a multiset of $m_i$ alleles, with within-sample counts $f_{i1},\dots,f_{ik_i}$. If the $M$ allele copies are assigned to the $M$ chromosome slots uniformly at random, then

$$P(G_1,\dots,G_n\mid f_1,\dots,f_K)=\binom{M}{f_1,\dots,f_K}^{-1}\prod_{i=1}^n\binom{m_i}{f_{i1},\dots,f_{ik_i}}=\frac{1}{M!}\prod_{l=1}^Kf_l!\ \prod_{i=1}^n\frac{m_i!}{\prod_{j=1}^{k_i}f_{ij}!}.$$

For a fully diploid sample ($m_i=2$ for all $i$) with $h$ heterozygous genotypes this reduces to

$$P(G_1,\dots,G_n\mid f_1,\dots,f_K)=2^h\binom{M}{f_1,\dots,f_K}^{-1}.$$

## Expansion

There are $\binom{M}{f_1,\dots,f_K}$ equally likely phased arrangements of the allele multiset over the $M$ slots, so each phased genotyping has probability equal to the reciprocal. An unphased genotyping is the union of the phased genotypings obtained by permuting alleles within each sample, of which there are $\prod_i\binom{m_i}{f_{i1},\dots,f_{ik_i}}$. For diploids a homozygote has one ordering and a heterozygote two, giving the factor $2^h$.

## Sources

- E. Garrison, G. Marth, "Haplotype-based variant detection from short-read sequencing", arXiv:1207.3907 (2012), Section 2.4.2, Equations (7)–(9), <https://doi.org/10.48550/arXiv.1207.3907>.
