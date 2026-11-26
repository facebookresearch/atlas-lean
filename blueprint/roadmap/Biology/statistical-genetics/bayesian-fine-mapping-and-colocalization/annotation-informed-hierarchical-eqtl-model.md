# Annotation-informed hierarchical model for cis-eQTL fine-mapping

For gene $k$ with expression levels $Y_k = (y_{ik})_i$ and candidate cis-SNPs $j = 1, \dots, J_k$ with genotypes $g_{ijk} \in \{0,1,2\}$, the single-SNP model is

$$y_{ik} = \mu + a_{jk}\, g_{ijk} + d_{jk}\, \mathbf 1(g_{ijk} = 1) + \varepsilon_{ijk}, \qquad \varepsilon_{ijk} \sim N(0, 1/\tau),$$

and the Bayes factor of SNP $j$ is $\mathrm{BF}_{jk} = P(Y_k \mid \text{SNP } j \text{ is the eQTN}) / P(Y_k \mid \text{no eQTN})$, computed analytically under normal-mixture priors on $(a_{jk}, d_{jk})$. Assume each gene has no cis-eQTN with probability $\Pi_0$ and exactly one with probability $\Pi_1 = 1 - \Pi_0$. Given one, it is SNP $j$ with prior probability $\pi_{jk}$, which depends on $L$ binary annotations $\delta_{jkl}$ (position bins relative to the transcription start and end sites, exon/intron status, ...) through

$$\eta_{jk} = \sum_{l=1}^L \lambda_l\, \delta_{jkl}, \qquad \pi_{jk} = \frac{e^{\eta_{jk}}}{\sum_{j'=1}^{J_k} e^{\eta_{j'k}}}.$$

Then, with $P_0(Y_k)$ the null likelihood,

$$\frac{P(Y_k \mid \Theta)}{P_0(Y_k)} = \Pi_0 + \Pi_1 \sum_{j=1}^{J_k} \pi_{jk}\, \mathrm{BF}_{jk},$$

and the parameters $\Theta = (\Pi_0, \Lambda, \dots)$ are fitted by maximizing $\sum_k \log\bigl(\Pi_0 + \Pi_1 \sum_j \pi_{jk} \mathrm{BF}_{jk}\bigr)$ over all genes (the $\log P_0$ terms do not depend on $\Theta$). The posterior probability that SNP $j$ is the eQTN of gene $k$ is

$$P(j \mid Y_k) = \frac{\Pi_1\, \pi_{jk}\, \mathrm{BF}_{jk}}{\Pi_0 + \Pi_1 \sum_{j'} \pi_{j'k}\, \mathrm{BF}_{j'k}}.$$

Sharing $\Lambda$ across genes learns where eQTNs typically lie. For two SNPs in perfect LD with equal Bayes factors, it then shifts posterior weight towards the SNP with the better-supported annotation.

## Depends on

- [Wakefield's approximate Bayes factor](wakefield-abf.md)
- [Posterior inclusion probability](pip.md)

## Expansion

The gene-level likelihood mixes the null and one-eQTN hypotheses: $P(Y_k) = \Pi_0 P_0 + \Pi_1 \sum_j \pi_{jk} P(Y_k \mid j)$. Dividing by $P_0$ turns every alternative likelihood into its Bayes factor. Because the $\pi_{jk}$ sum to one within a gene, the logistic link is a softmax over the gene's SNPs. Bayes' rule on the same mixture gives the per-SNP posterior.

## Sources

- J.-B. Veyrieras, S. Kudaravalli, S. Y. Kim, E. T. Dermitzakis, Y. Gilad, M. Stephens and J. K. Pritchard, *High-resolution mapping of expression-QTLs yields insight into human gene regulation*, PLoS Genet. 4 (2008), e1000214, <https://doi.org/10.1371/journal.pgen.1000214>, PMCID PMC2556086, Methods, "Hierarchical Model": Eq. (2) (Bayesian regression model), Eq. (3) (Bayes factor), Eqs. (4)–(5) (zero-or-one eQTN mixture), Eqs. (6)–(7) (annotation-dependent logistic prior) and Eqs. (8)–(10) (likelihood and its maximization). The displayed formulas are written out from the verbal definitions there.
