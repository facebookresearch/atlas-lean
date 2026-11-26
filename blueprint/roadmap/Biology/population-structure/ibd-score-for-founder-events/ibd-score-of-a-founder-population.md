# IBD score of a founder population

Let a group be represented by $n \ge 2$ diploid individuals, giving $2n$ phased haplotypes labeled by $(k, h)$ with individual $k \in \{1, \dots, n\}$ and haplotype $h \in \{1, 2\}$. For an unordered pair of haplotypes from **different** individuals, let $L$ denote the total genetic length of the identity-by-descent segments they share whose individual lengths lie in a window $[\ell_{\min}, \ell_{\max}]$ (Nakatsuka et al. use $3$–$20$ cM: the lower bound removes short, unreliable or very old segments, the upper bound removes segments from recent relatedness). The **IBD score** of the group is

$$\mathrm{IBD}_n = \frac{\sum_{\text{between-individual haplotype pairs}} L}{\binom{2n}{2} - n}.$$

**Proposition.** (i) The denominator counts exactly the between-individual haplotype pairs:

$$\binom{2n}{2} - n = 2n(n - 1) = 4\binom{n}{2}.$$

(ii) If the $2n$ haplotypes are exchangeable (for example, a random sample from a group without internal structure, after removal of close relatives), so that every between-individual pair has the same expected windowed IBD length $\lambda$, then $\mathbb{E}[\mathrm{IBD}_n] = \lambda$ for every $n \ge 2$. Thus the score is an unbiased, sample-size-free estimate of the expected windowed IBD sharing between two random haplotypes from distinct members of the group, and ratios of scores between groups (for example, relative to Finns) compare founder-event strengths.

## Expansion

Among the $\binom{2n}{2}$ unordered pairs of haplotypes, exactly $n$ pair the two haplotypes of one individual (self-matches, which reflect inbreeding from consanguineous marriage rather than the founder event and are excluded); each of the $\binom n2$ pairs of individuals contributes $2 \times 2 = 4$ haplotype pairs, so $\binom{2n}{2} - n = 4\binom n2$. Part (ii) is linearity of expectation over the $4\binom n2$ terms. A stronger or more recent bottleneck raises the probability that two haplotypes descend from a common founder within the last $\sim 100$ generations and so inflates windowed IBD; the paper validates by coalescent simulation that groups with twice the Finnish bottleneck strength are detected with sensitivity above $95\%$ from about five samples, computes block-jackknife standard errors over chromosomes, and finds 81 South Asian groups with scores exceeding both Finns and Ashkenazi Jews.

## Sources

- N. Nakatsuka, P. Moorjani, N. Rai et al., "The promise of discovering population-specific disease-associated genes in South Asia", Nature Genetics 49 (2017), main text (IBD score definition) and Online Methods "Phasing, IBD Detection, and IBD Score Algorithm", <https://doi.org/10.1038/ng.3917>, PMCID PMC5675555.
