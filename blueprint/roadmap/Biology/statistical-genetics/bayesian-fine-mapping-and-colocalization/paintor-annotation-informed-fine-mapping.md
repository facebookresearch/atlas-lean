# PAINTOR: annotation-informed fine-mapping of causal variants across loci

Let loci $j = 1, \dots, J$ contain $m_j$ SNPs with observed association Z-scores $Z_j \in \mathbb R^{m_j}$ and LD (correlation) matrices $\Sigma_j$. Let $C_j \in \{0,1\}^{m_j}$ indicate which SNPs are causal and $\lambda_j \in \mathbb R^{m_j}$ be the non-centrality parameters (standardized effect sizes) of the SNPs. SNP $i$ in locus $j$ has binary functional annotations $a_{ijk}$, $k = 1, \dots, K$, and annotation effects $\gamma = (\gamma_0, \dots, \gamma_K)$ enter through a logistic prior, independently across SNPs:

$$\mathbb P(C_{ij} = 1 \mid \gamma) = \pi_{ij}(\gamma) = \frac{1}{1 + \exp\!\big(-\gamma_0 - \sum_{k} \gamma_k a_{ijk}\big)}, \qquad \mathbb P(C_j \mid \gamma) = \prod_i \pi_{ij}^{C_{ij}}(1 - \pi_{ij})^{1 - C_{ij}}.$$

Given the causal configuration, the Z-scores follow the multivariate normal model

$$Z_j \mid C_j \sim \mathcal N\big(\Sigma_j(\lambda_j \circ C_j),\; \Sigma_j\big),$$

where $\circ$ is the elementwise product. The likelihood of the data is

$$L(\gamma) = \prod_{j=1}^J \sum_{C_j} \mathbb P(Z_j \mid C_j)\, \mathbb P(C_j \mid \gamma),$$

summing over configurations with at most a fixed small number of causal SNPs per locus. Posterior configuration probabilities follow from Bayes' theorem,

$$\mathbb P(C_j \mid Z_j, \gamma) = \frac{\mathbb P(Z_j \mid C_j)\mathbb P(C_j \mid \gamma)}{\sum_{C'} \mathbb P(Z_j \mid C')\mathbb P(C' \mid \gamma)},$$

and the posterior probability that SNP $i$ is causal is the sum over configurations with $C_{ij} = 1$. The annotation effects $\gamma$ are estimated by maximum likelihood with an EM algorithm whose M-step objective

$$Q(\gamma) = \sum_j \sum_{C_j} \mathbb P(C_j \mid Z_j, \gamma^{\mathrm{old}}) \log \mathbb P(C_j \mid \gamma)$$

is concave in $\gamma$. The significance of an annotation is assessed by the likelihood-ratio statistic comparing fits with and without it.

## Expansion

Because $\log \mathbb P(C_j \mid \gamma) = \sum_i [C_{ij} \log \pi_{ij} + (1 - C_{ij})\log(1 - \pi_{ij})]$, the M-step is a logistic regression of posterior causal probabilities on annotations, a concave problem with gradient $\sum_{i,j}(\mathbb P(C_{ij}=1\mid Z_j) - \pi_{ij})\,(1, a_{ij1}, \dots, a_{ijK})$; Kichaev et al. maximize it with L-BFGS while holding the non-centrality parameters fixed. Pooling the annotation model across loci borrows strength and avoids overfitting any single locus. With $\gamma_k = 0$ for all annotations the prior is a constant per-SNP causal probability and the model reduces to a standard multi-causal fine-mapping likelihood. In simulations and lipid meta-analysis data the annotation-weighted posteriors reduce the number of SNPs needed to capture the causal variants relative to annotation-blind fine-mapping.

## Sources

- G. Kichaev, W.-Y. Yang, S. Lindstrom, F. Hormozdiari, E. Eskin, A. L. Price, P. Kraft, B. Pasaniuc, "Integrating functional data to prioritize causal variants in statistical fine-mapping studies", PLoS Genetics 10 (2014), e1004722, <https://doi.org/10.1371/journal.pgen.1004722> (PMC4214605), Methods "PAINTOR probabilistic model" (Equations 1–5), "Model fitting" and "Measuring enrichment significance".
