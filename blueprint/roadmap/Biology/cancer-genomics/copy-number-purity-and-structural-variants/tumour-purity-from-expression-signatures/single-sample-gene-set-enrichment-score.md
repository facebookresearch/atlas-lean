# Single-sample gene-set enrichment score

Let a sample be described by expression values $x_1, \dots, x_N$ on $N$ genes, and let $S \subseteq \{1, \dots, N\}$ be a gene signature with $|S| = n$ and complement $S^c$ of size $N - n$. Rank the genes by decreasing expression, so that $r(i) \in \{1, \dots, N\}$ is the rank of gene $i$, and for a position $k \in \{1, \dots, N\}$ define the two empirical distribution functions

$$F_S(k) = \frac{1}{n} \,\#\{ i \in S : r(i) \le k \}, \qquad F_{S^c}(k) = \frac{1}{N - n} \,\#\{ i \in S^c : r(i) \le k \}.$$

The **single-sample enrichment score** of $S$ in that sample is the integrated difference of the two distribution functions along the rank list,

$$\mathrm{ES}(S) = \sum_{k=1}^{N} \big( F_S(k) - F_{S^c}(k) \big).$$

Both $F_S$ and $F_{S^c}$ are nondecreasing with $F_S(N) = F_{S^c}(N) = 1$, so $\mathrm{ES}(S)$ is a signed area between two curves that start at or above $0$ and end at $1$: it is positive when the genes of $S$ sit near the top of the rank list and negative when they sit near the bottom. Unlike the classical enrichment statistic, which compares two phenotype groups, this score is computed from the absolute expression ranks of one sample, so it is defined for a single profile. The variant used in practice weights the running sum by a power of the rank-ordered expression values; the unweighted form above is the one described for the stromal and immune signatures below.

Two such scores, one for a stromal signature and one for an immune signature, are summed into a combined score,

$$\mathrm{ESTIMATE} = \mathrm{ES}(S_{\text{stromal}}) + \mathrm{ES}(S_{\text{immune}}),$$

which is used as a surrogate for the non-malignant fraction of a tumour sample.

## Expansion

Writing $d_k = F_S(k) - F_{S^c}(k)$, the increment $d_k - d_{k-1}$ equals $1/n$ when the gene at rank $k$ lies in $S$ and $-1/(N-n)$ otherwise, which is exactly the running sum of the Kolmogorov–Smirnov style enrichment walk; $\mathrm{ES}(S)$ is the sum of that walk rather than its extreme value, so it aggregates the whole displacement instead of its maximum, which makes it less sensitive to a single extreme rank. Because the score depends on the expression values only through their ranks, it is invariant under any strictly increasing transformation of the sample's expression values, which is what allows scores from different platforms (arrays of different design, or sequencing) to be compared after each sample is rank-normalized separately.

## Sources

- K. Yoshihara, M. Shahmoradgoli, E. Martínez et al., "Inferring tumour purity and stromal and immune cell admixture from expression data", Nature Communications 4 (2013), 2612, Methods ("ESTIMATE algorithm" and "Stromal, immune and ESTIMATE scores"), <https://doi.org/10.1038/ncomms3612>, PMCID PMC3826632.
- D. A. Barbie, P. Tamayo, J. S. Boehm et al., "Systematic RNA interference reveals that oncogenic KRAS-driven cancers require TBK1", Nature 462 (2009), 108–112 (single-sample enrichment statistic), <https://doi.org/10.1038/nature08460>.
