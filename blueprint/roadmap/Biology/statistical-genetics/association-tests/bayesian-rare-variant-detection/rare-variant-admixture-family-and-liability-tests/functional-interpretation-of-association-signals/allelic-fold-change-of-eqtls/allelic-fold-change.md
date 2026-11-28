# Allelic fold change

Let a cis-regulatory variant have reference allele $\mathrm{ref}$ and alternative allele $\mathrm{alt}$, and suppose each haplotype contributes additively to the total expression of the gene in a diploid cell: a reference haplotype contributes $c > 0$ and an alternative haplotype contributes $kc$, with $k > 0$. Then the expected expression of an individual with $g \in \{0,1,2\}$ alternative alleles is

$$e(g) = (2 - g)\,c + g\,k\,c,$$

so that $e(0) = 2c$, $e(1) = (1 + k)c$ and $e(2) = 2kc$. The **allelic fold change** of the eQTL is

$$\mathrm{aFC} = \log_2 k = \log_2 \frac{e(2)}{e(0)}.$$

In a heterozygote the ratio of expected alternative-allele to reference-allele expression is $kc/c = k$, so the same parameter can be estimated from allele-specific expression.

## Expansion

The model is additive on the linear scale of transcript abundance, not on the log scale: $\log e(g)$ is not linear in $g$ unless $k = 1$, so regressing log expression on genotype gives an effect that only approximates $\mathrm{aFC}$ and saturates for large fold changes. Fitting $c$ and $k$ by nonlinear least squares on expression (after covariate adjustment) yields an effect size with a direct biological reading, a symmetric scale ($\mathrm{aFC} \mapsto -\mathrm{aFC}$ when the allele labels are swapped) and comparability between genes with different baseline expression. The GTEx Consortium used aFC for the primary eVariant of each eGene and found that 17.4% of eGenes had median effect sizes of at least twofold across tissues; aFC estimated from allele-specific expression agreed closely with aFC from total expression (mean Spearman $\rho = 0.82$, mean ratio $0.937$).

## Sources

- GTEx Consortium, "Genetic effects on gene expression across human tissues", Nature 550 (2017), 204–213, <https://doi.org/10.1038/nature24277> (PMC5776756), section on cis-eQTL effect sizes and allele-specific expression.
- P. Mohammadi, S. E. Castel, A. A. Brown, T. Lappalainen, "Quantifying the regulatory effect size of cis-acting genetic variation using allelic fold change", Genome Research 27 (2017), 1872–1884, <https://doi.org/10.1101/gr.216747.116>.
