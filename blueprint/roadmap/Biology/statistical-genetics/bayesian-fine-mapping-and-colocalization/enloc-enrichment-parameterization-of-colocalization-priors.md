# ENLOC enrichment parameterization of colocalization priors

For a variant let $d \in \{0,1\}$ indicate a causal effect on a molecular trait (for example expression of a gene) and $\gamma \in \{0,1\}$ a causal effect on a complex trait. SNP-level probabilistic colocalization computes

$$\Pr(\gamma = 1, d = 1 \mid \text{eQTL data}, \text{GWAS data}) \propto \Pr(\gamma = 1, d = 1)\, P(\text{eQTL data}, \text{GWAS data} \mid d = 1, \gamma = 1),$$

and with non-overlapping cohorts the likelihood factorizes as $P(\text{eQTL data} \mid d)\, P(\text{GWAS data} \mid \gamma)$.

**Enrichment parameterization.** Write $\Pr(\gamma = 1, d = 1) = \Pr(\gamma = 1 \mid d = 1)\, p_d$ with $p_d = \Pr(d = 1)$, and

$$\operatorname{logit} \Pr(\gamma = 1 \mid d) = \alpha_0 + \alpha_1 d,$$

so $\alpha_1$ is the log odds ratio of molecular QTLs among complex-trait causal variants. The triple $(p_d, \alpha_0, \alpha_1)$ determines $p_\gamma = \Pr(\gamma = 1)$.

**Equivalence with other methods.** With coloc's per-SNP priors $p_{12} = \Pr(\gamma=1, d=1)$, $p_{\mathrm{mol}} = \Pr(\gamma=0, d=1)$ and $p_{\mathrm{cx}} = \Pr(\gamma=1, d=0)$, and $p_{00} = 1 - p_{\mathrm{mol}} - p_{\mathrm{cx}} - p_{12}$,

$$p_d = p_{\mathrm{mol}} + p_{12}, \qquad \alpha_0 = \log\frac{p_{\mathrm{cx}}}{p_{00}}, \qquad \alpha_1 = \log\frac{p_{12}\, p_{00}}{p_{\mathrm{mol}}\, p_{\mathrm{cx}}}.$$

eCAVIAR's prior independence of $\gamma$ and $d$ is the case $\alpha_1 = 0$, that is $\Pr(\gamma=1, d=1) = p_\gamma p_d$.

**Sensitivity.** For $\alpha_1$ in the empirically relevant range $[0, 5]$, colocalization probabilities of SNPs with strong or with weak marginal evidence in both studies are stable, while SNPs with moderate evidence in either study are highly sensitive to $\alpha_1$. Aggressive enrichment priors inflate false colocalizations, and $\alpha_1 = 0$ costs power, so the source recommends estimating $(p_d, \alpha_0, \alpha_1)$ from the data, as ENLOC/fastENLOC do by multiple imputation.

## Depends on

- [Colocalization prior parameters](coloc-prior.md)

## Expansion

The conversion is the definition of the logistic model: $\Pr(\gamma=1 \mid d=0) = p_{\mathrm{cx}}/(p_{\mathrm{cx}} + p_{00})$ gives $\alpha_0$, and the odds ratio of the $2 \times 2$ table of $(\gamma, d)$ gives $\alpha_1$. Coloc additionally assumes at most one causal variant per trait in a locus, which makes the likelihood computable from marginal statistics; when the molecular trait has allelic heterogeneity this costs power (in the source's simulations coloc had about half the power of fastENLOC), while both methods controlled the false discovery rate when supplied with correct priors.

## Sources

- A. Hukku, M. Pividori, F. Luca, R. Pique-Regi, H. K. Im and X. Wen, "Probabilistic colocalization of genetic variants from complex and molecular traits: promise and limitations", *American Journal of Human Genetics* 108 (2021), 25–35, <https://doi.org/10.1016/j.ajhg.2020.11.012> (PMC7820626; Equations 1–5, sections "Statistical framework of probabilistic colocalization analysis" and "Specification of enrichment prior"; the coloc parameter conversion is rederived from Equation 4).
