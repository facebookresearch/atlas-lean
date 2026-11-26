# LOD score of autozygosity for calling runs of homozygosity

Let an individual have genotypes $g_1, \dots, g_n$ at a window of $n$ consecutive biallelic SNPs, with population allele frequencies $p_k, q_k = 1 - p_k$ at SNP $k$, and let $\varepsilon$ be a small rate of genotyping error and mutation. The **LOD score of autozygosity** of the window is

$$\mathrm{LOD} = \sum_{k=1}^{n}\log_{10}\frac{\Pr(g_k \mid \text{autozygous})}{\Pr(g_k \mid \text{not autozygous})},$$

where, under non-autozygosity, genotypes follow Hardy–Weinberg proportions $(p_k^2, 2p_kq_k, q_k^2)$, and under autozygosity both alleles are a single ancestral allele drawn with frequency $p_k$ or $q_k$, except that with probability $\varepsilon$ the genotype is drawn as under non-autozygosity. In this standard form

$$\Pr(AA \mid \text{auto}) = (1-\varepsilon)p_k + \varepsilon p_k^2, \qquad \Pr(Aa \mid \text{auto}) = 2\varepsilon p_kq_k, \qquad \Pr(aa \mid \text{auto}) = (1-\varepsilon)q_k + \varepsilon q_k^2,$$

so a homozygote contributes $\log_{10}\big((1-\varepsilon)/p_k + \varepsilon\big) > 0$ (rare homozygotes count more) and a heterozygote contributes $\log_{10}\varepsilon < 0$.

**Calling procedure.** Slide the window along each chromosome in steps of $m$ SNPs; across all windows and individuals of a population the LOD scores are bimodal, and the population-specific threshold is placed at the local minimum between the two modes of a kernel density estimate. Windows above the threshold are called autozygous, and contiguous called windows are merged into one run of homozygosity (ROH). Allele frequencies are estimated from a fixed number of resampled alleles per population (for example $40$), so that thresholds are comparable across populations of different sample sizes; a SNP at which the individual carries an allele of estimated frequency $0$ is treated as missing (contribution $0$ to the LOD).

## Remarks

Within a truly autozygous segment the two haplotypes are identical by descent, so heterozygotes occur only through error or new mutation, with probability of order $\varepsilon$; outside, heterozygosity is near $2p_kq_k$. The log ratio for a homozygote $AA$ is $\log_{10}\big(((1-\varepsilon)p_k + \varepsilon p_k^2)/p_k^2\big) = \log_{10}\big((1-\varepsilon)/p_k + \varepsilon\big)$, positive whenever $p_k < 1$, and a single heterozygote costs $\log_{10}\varepsilon \approx -3$ for $\varepsilon = 10^{-3}$, so occasional errors do not break a long run but a cluster of heterozygotes does. Summing independent per-SNP log ratios ignores linkage disequilibrium among SNPs in the window; because common haplotypes in high LD look homozygous without recent shared ancestry, the lower mode of the LOD distribution and short calls partly reflect LD, which is why the window width is chosen as the largest value giving a clearly bimodal distribution in every population (60 SNPs on a dense array).

## Depends on

- [Hardy–Weinberg frequency $p^2$ of the AA homozygote](../../hardy-weinberg-law/offspring-true-true.md)
- [Hardy–Weinberg proportions](../../hardy-weinberg-law/offspring-apply.md)
- [Genotype frequencies of an inbred individual](../genotype-frequencies-under-inbreeding.md)

## Sources

- T. J. Pemberton, D. Absher, M. W. Feldman, R. M. Myers, N. A. Rosenberg and J. Z. Li, "Genomic Patterns of Homozygosity in Worldwide Human Populations", *American Journal of Human Genetics* 91 (2012), 275–292, Material and Methods (identification of ROH by windowed LOD scores), <https://doi.org/10.1016/j.ajhg.2012.06.014> (PMC3415543).
- K. W. Broman and J. L. Weber, "Long homozygous chromosomal segments in reference families from the Centre d'Étude du Polymorphisme Humain", *American Journal of Human Genetics* 65 (1999), 1493–1500, <https://doi.org/10.1086/302661>.
