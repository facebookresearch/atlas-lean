# Admixture-constrained likelihood-ratio test for selection

At one SNP, let $A$ present-day populations have allele frequencies $p_{\mathrm{mod}} \in [0,1]^A$ and $B$ ancient source populations have frequencies $p_{\mathrm{anc}} \in [0,1]^B$. Suppose the present-day populations are modeled as mixtures of the sources with known proportions, $p_{\mathrm{mod}} = C p_{\mathrm{anc}}$, where $C$ is an $A \times B$ matrix with nonnegative rows summing to $1$. With data $D_j$ for population $j$ and the [read-count allele-frequency log-likelihood](allele-frequency-likelihood-from-read-counts-and-genotypes.md) $\ell(p_j; D_j)$, the joint log-likelihood of $\bar p = (p_{\mathrm{anc}}, p_{\mathrm{mod}})$ is

$$\ell(\bar p; \bar D) = \sum_{j=1}^{A+B} \ell(p_j; D_j).$$

The test of

$$H_0: p_{\mathrm{mod}} = C p_{\mathrm{anc}} \qquad \text{versus} \qquad H_1: p_{\mathrm{mod}} \text{ unconstrained}$$

uses the statistic

$$\Lambda = 2\Big(\sup_{H_1} \ell(\bar p; \bar D) - \sup_{H_0} \ell(\bar p; \bar D)\Big),$$

referred to a $\chi^2_A$ distribution. Genome-wide inflation from unmodeled ancestry or extra drift is removed by genomic control: every $\Lambda$ is divided by a constant $\lambda$ chosen so that the median of the corrected statistics matches the median of $\chi^2_A$. Large corrected statistics indicate present-day frequencies that cannot be explained by mixing the ancient sources, a signature of selection since admixture.

## Depends on

- [Allele-frequency likelihood from read counts and hard genotype calls](allele-frequency-likelihood-from-read-counts-and-genotypes.md)

## Expansion

Under $H_1$ the present-day frequencies are $A$ free parameters; under $H_0$ they are determined by the ancient ones, so the constraint removes $A$ degrees of freedom and Wilks' theorem gives the $\chi^2_A$ reference when the ancient and present-day samples are large enough and frequencies are interior. The mixture proportions are estimated beforehand from genome-wide $f_4$-statistics with outgroups, so neutral SNPs follow the model up to drift. Mathieson et al. used three ancient sources (hunter-gatherers, early farmers and steppe pastoralists) and four present-day European populations, estimated $\lambda = 1.38$ from SNPs outside a set of potentially functional variants, and found twelve genome-wide significant loci, including the lactase persistence variant; potentially functional SNPs as a class were more inconsistent with the model than neutral SNPs.

## Sources

- I. Mathieson, I. Lazaridis, N. Rohland, et al., "Genome-wide patterns of selection in 230 ancient Eurasians", Nature 528 (2015), 499–503, <https://doi.org/10.1038/nature16152> (PMC4918750), main text "Twelve signals of selection" and Methods "Genome-wide scan for selection".
