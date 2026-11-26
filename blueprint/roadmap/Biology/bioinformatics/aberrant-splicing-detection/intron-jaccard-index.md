# Intron Jaccard index

For an RNA-seq sample $i$ and an intron $j$ with donor site $d_j$ and acceptor site $a_j$, let $D_{ij}$ be the set of **donor-associated reads**: split reads using donor $d_j$ and non-split reads spanning the exon–intron boundary at $d_j$. Let $A_{ij}$ be the analogous set of **acceptor-associated reads** at $a_j$.

**Definition.** The intron Jaccard index is
$$J_{ij} = \frac{|D_{ij} \cap A_{ij}|}{|D_{ij} \cup A_{ij}|} = \frac{s_{ij}}{\sum_{d \in L_j} s_{id} + \sum_{a \in R_j} s_{ia} + \sum_{t \in \{d_j, a_j\}} u_{it} - s_{ij}},$$
where $s_{ij}$ is the number of split reads mapping exactly to intron $j$, $L_j$ ($R_j$) is the set of introns using donor $d_j$ (acceptor $a_j$), and $u_{it}$ is the number of non-split reads spanning the exon–intron boundary at splice site $t$. Thus $J_{ij} \in [0,1]$ is the fraction of reads at either splice site that support splicing of exactly this intron.

**Outlier model (FRASER 2.0).** With numerator $k_{ij}$ and denominator $n_{ij}$ of $J_{ij}$, the logit-transformed values $x_{ij} = \operatorname{logit}\bigl((k_{ij} + \alpha)/(n_{ij} + 2\alpha)\bigr)$, with pseudocount $\alpha$, are fed to a denoising autoencoder that captures sample covariation. Each observed $k_{ij}$ is then tested against a beta-binomial distribution with $n_{ij}$ trials and mean given by the autoencoder's predicted $J_{ij}$. Intron-level $p$-values are Holm-corrected within each gene and sample, the minimum is taken as the gene-level $p$-value, and Benjamini–Yekutieli FDR control is applied across genes within each sample.

## Expansion

The donor and acceptor read sets intersect exactly in the split reads of intron $j$, so the inclusion–exclusion count gives the closed form. A single index captures alternative donor and acceptor usage, exon skipping, exon truncation or elongation, exon creation and intron retention, which the older FRASER metrics $\psi_5$, $\psi_3$ and $\theta$ split across three partly redundant statistics. Because its denominator pools both splice sites, a rare alternative donor that leaves the canonical intron dominant changes $J$ little, which removes many low-impact outliers. On GTEx, the method called about $10$ times fewer splicing outliers with about $10$-fold enrichment for candidate rare splice-disrupting variants.

## Sources

- I. F. Scheller, K. Lutz, C. Mertes, V. A. Yépez and J. Gagneur, "Improved detection of aberrant splicing with FRASER 2.0 and the intron Jaccard index", *American Journal of Human Genetics* 110 (2023), 2056–2067, <https://doi.org/10.1016/j.ajhg.2023.10.014> (PMC10716352; Material and methods, sections "Splicing quantification with the intron Jaccard index", "Denoising autoencoder" and "Multiple-testing correction and effect-size cutoff"; Figure 1).
