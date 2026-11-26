# Leading-edge fraction test for gene-set enrichment

Let every gene $g$ in the genome have a [corrected gene p-value](best-snp-gene-score-with-confounder-regression.md) $p_g$, and fix a cutoff $c$ equal to a chosen percentile of all gene p-values (MAGENTA uses the 95th percentile of gene scores, that is, the 5% most significant genes). For a gene set $\mathcal S$, first drop genes without SNPs and, among genes of $\mathcal S$ whose best SNP is the same SNP, keep only the gene with the most significant score; call the remaining set $\mathcal S'$ with $|\mathcal S'| = s$. The **leading-edge fraction** is

$$\phi(\mathcal S') = \frac{1}{s}\,\big|\{g \in \mathcal S' : p_g < c\}\big|.$$

Under the null that the gene-score ranks of the set are randomly distributed, $\phi(\mathcal S')$ is compared with the leading-edge fractions of $B$ random gene sets $\mathcal R_1, \dots, \mathcal R_B$ of the same effective size $s$, drawn from the whole genome and pruned in the same way, and the enrichment p-value is

$$p_{\mathcal S} = \frac{1}{B}\,\big|\{b : \phi(\mathcal R_b) \ge \phi(\mathcal S')\}\big|.$$

Multiple gene sets are corrected by Bonferroni.

## Depends on

- [Best-SNP gene score with confounder regression and the Šidák alternative](best-snp-gene-score-with-confounder-regression.md)

## Expansion

The statistic counts how many genes of the set fall in the top tail of the genome-wide gene-score distribution, so it targets sets in which many genes carry modest association signal rather than a single strong hit; for large genomes and random sets drawn without replacement, $s\,\phi$ is approximately hypergeometric, but MAGENTA uses resampling, which also respects the pruning. Pruning genes that share a best SNP prevents one association signal from being counted several times when neighbouring genes in the same set lie in the same LD region. Segrè et al. chose the 95th-percentile cutoff as the most powerful of five tested in simulations, validated the method on lipid meta-analyses, and found no enrichment of type 2 diabetes associations among mitochondria-related gene sets; a one-tailed Mann–Whitney rank-sum version gave the same conclusion.

## Sources

- A. V. Segrè, DIAGRAM Consortium, MAGIC investigators, L. Groop, V. K. Mootha, M. J. Daly, D. Altshuler, "Common inherited variation in mitochondrial genes is not enriched for associations with type 2 diabetes or related glycemic traits", PLoS Genetics 6 (2010), e1001058, <https://doi.org/10.1371/journal.pgen.1001058> (PMC2920848), Materials and Methods, "Step 4: Gene set enrichment analysis of genome-wide association data".
