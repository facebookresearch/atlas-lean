# Diploid HMM of a localized haplotype-cluster model and the Beagle phasing sampler

Let $G$ be a [localized haplotype-cluster model](localized-haplotype-cluster-model.md) with edge classes $L_1,\dots,L_M$ and induced haploid initial and transition probabilities $P(e)$, $P(e_1 \mid e_2)$.

**Diploid HMM.** The hidden state at marker $m$ is an *ordered* pair $s_m = (e_1,e_2) \in L_m \times L_m$; it emits, with probability $1$, the unordered genotype formed by the labels of $e_1$ and $e_2$. Under Hardy–Weinberg equilibrium the diploid initial and transition probabilities are products of haploid ones:

$$P(e_1,e_2) = P(e_1)P(e_2), \qquad P\big((e_1,e_2) \mid (e_3,e_4)\big) = P(e_1 \mid e_3)\,P(e_2 \mid e_4).$$

For an individual with observed genotypes $g_1,\dots,g_M$, the emission $P(g_m \mid s_m) \in \{0,1\}$ indicates consistency of $g_m$ with the labels of $s_m$; a fully missing genotype has $P(g_m \mid s_m) = 1$, and a genotype with one missing allele has $P(g_m \mid s_m) = 1$ iff the observed allele labels one of the two edges.

**Forward variables.** $\alpha_m(s_m) = P(g_1,\dots,g_m,s_m)$ satisfy

$$\alpha_1(s_1) = P(s_1)P(g_1 \mid s_1), \qquad \alpha_{m+1}(s_{m+1}) = P(g_{m+1} \mid s_{m+1}) \sum_{s_m \in L_m \times L_m} \alpha_m(s_m)\, P(s_{m+1} \mid s_m).$$

**Backward sampling.** Draw $s_M$ with probability proportional to $\alpha_M(s_M)$, and for $m = M-1,\dots,1$ draw $s_m$ given $s_{m+1},\dots,s_M$ with probability

$$P(s_m \mid s_{m+1},\dots,s_M, g_1,\dots,g_M) = \frac{\alpha_m(s_m)\,P(s_{m+1} \mid s_m)}{\sum_{s} \alpha_m(s)\,P(s_{m+1} \mid s)}.$$

The sampled path is an exact draw from the posterior of the hidden path, i.e. an ordered haplotype pair consistent with the genotypes (including imputed missing alleles). Replacing sampling by the Viterbi recursion gives the most likely haplotype pair.

**Beagle phasing algorithm.** Starting from randomly phased (and randomly imputed) genotypes, iterate: (i) fit a localized haplotype-cluster model to the current haplotypes; (ii) for each individual, sample a new haplotype pair from the diploid HMM conditional on its genotypes. The final iteration outputs Viterbi haplotypes. Marker order is reversed on alternate iterations, and $R \ge 1$ haplotype pairs per individual may be sampled.

## Depends on

- [Localized haplotype-cluster model and its induced haplotype HMM](localized-haplotype-cluster-model.md)

## Expansion

By the Markov property $P(s_m \mid s_{m+1:M}, g_{1:M}) \propto P(s_m, g_{1:m})\,P(s_{m+1} \mid s_m)$, since given $s_{m+1}$ the later genotypes are independent of $s_m$; this is the displayed backward kernel. The pair is ordered, so heterozygous genotypes need no factor of $2$. The alternation of fitting and sampling is a stochastic EM scheme.

## Sources

- S. R. Browning and B. L. Browning, "Rapid and Accurate Haplotype Phasing and Missing-Data Inference for Whole-Genome Association Studies By Use of Localized Haplotype Clustering", The American Journal of Human Genetics 81 (2007), 1084–1097, <https://doi.org/10.1086/521987> (PMC2265661). Methods, sections "The Induced HMM", "Sampling from an HMM", "The Beagle Phasing Algorithm"; Appendix A.
