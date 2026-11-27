# SNP association conditioned on local ancestry

Consider a case–control sample from a two-way admixed population whose ancestral populations are labelled $A$ and $E$. At a candidate biallelic SNP each individual has a local ancestry state $X \in \{AA, AE, EE\}$ giving the number of chromosomes of each ancestry at the locus, and a phenotype $Y \in \{0, 1\}$. Let $p_A, p_E$ be the reference-allele frequencies in controls on chromosomes of ancestry $A$ and $E$, and let $R$ be the allelic odds ratio, assumed equal across ancestries.

Write $RR_{X,Y}, RV_{X,Y}, VV_{X,Y}$ for the numbers of individuals with local ancestry $X$ and phenotype $Y$ that carry $2, 1, 0$ reference alleles, and $p_{a,Y}$ for the reference-allele frequency on chromosomes of ancestry $a \in \{A, E\}$ in phenotype group $Y$: $p_{a,0} = p_a$ in controls and the odds-ratio-tilted frequency

$$p_{a,1} = \frac{R\, p_a}{R\, p_a + (1 - p_a)}$$

in cases. The likelihood is the allele-count likelihood

$$
\begin{aligned}
L(R, p_A, p_E) = {} & \prod_{Y} p_{A,Y}^{2RR_{AA,Y}+RV_{AA,Y}}\,(1-p_{A,Y})^{2VV_{AA,Y}+RV_{AA,Y}} \\
& \cdot \prod_{Y} p_{A,Y}^{RR_{AE,Y}+0.5RV_{AE,Y}}\,(1-p_{A,Y})^{VV_{AE,Y}+0.5RV_{AE,Y}}\; p_{E,Y}^{RR_{AE,Y}+0.5RV_{AE,Y}}\,(1-p_{E,Y})^{VV_{AE,Y}+0.5RV_{AE,Y}} \\
& \cdot \prod_{Y} p_{E,Y}^{2RR_{EE,Y}+RV_{EE,Y}}\,(1-p_{E,Y})^{2VV_{EE,Y}+RV_{EE,Y}},
\end{aligned}
$$

with $Y$ ranging over $\{0, 1\}$. An $AA$ or $EE$ individual contributes both of its alleles to the frequency of its single ancestry, and a heterozygote ($RV$) with local ancestry $AE$, whose phase is not known, is credited with half a reference allele and half a variant allele on each ancestry, that is, with the factor $\bigl[p_{A,Y}(1-p_{A,Y})\,p_{E,Y}(1-p_{E,Y})\bigr]^{1/2}$ rather than the phase sum $p_{A,Y}(1-p_{E,Y}) + (1-p_{A,Y})\,p_{E,Y}$. Conditioning on $X$ means the frequency used for each chromosome is the one of its own ancestry, so stratification by ancestry — both global and local — cannot create a spurious allele-frequency difference between cases and controls.

The statistic is the likelihood-ratio test of $R = 1$ against $R \neq 1$, with $p_A, p_E$ profiled out as nuisance parameters,

$$\chi^2_{\mathrm{SNP1}} = 2 \log \frac{\max_{R, p_A, p_E} L(R, p_A, p_E)}{\max_{p_A, p_E} L(1, p_A, p_E)} \;\sim\; \chi^2_1 \text{ under } R = 1 .$$

Three parameters are maximized; because a one-dimensional section of the log likelihood in the odds ratio can be very steep, coordinatewise optimization with a one-dimensional search, falling back on bisection, is used in practice.

This score is the admixed-population analogue of an association test run inside a single ancestral population: it uses only the fine-scale correlation between the candidate SNP and the causal variant, and discards the information carried by the ancestry of the surrounding chromosomal segment.

## Expansion

Tilting an allele frequency by an odds ratio, $p \mapsto Rp/(Rp + 1 - p)$, is the retrospective form of a logistic model with per-allele effect $\log R$: it is the case frequency implied by multiplicative penetrance on the allele, and it keeps the frequency in $(0,1)$ for every $R > 0$. Treating $p_A$ and $p_E$ as free is what makes the test robust; the price is two extra nuisance parameters per SNP and the loss of the case-only admixture signal, which lives entirely in the distribution of $X$ that this likelihood conditions on. Simulations on real admixed genotypes put this score at lower power than a trend test corrected only for genome-wide ancestry, because the trend test implicitly uses part of the admixture signal, and lower still than a statistic that models both sources jointly.

## Sources

- B. Pasaniuc, N. Zaitlen, G. Lettre et al., "Enhanced statistical tests for GWAS in admixed populations: assessment using African Americans from CARe and a Breast Cancer Consortium", PLoS Genetics 7 (2011), e1001371, Methods ("SNP1: SNP association conditioned on local ancestry") and Text S1, <https://doi.org/10.1371/journal.pgen.1001371>, PMCID PMC3080860.
