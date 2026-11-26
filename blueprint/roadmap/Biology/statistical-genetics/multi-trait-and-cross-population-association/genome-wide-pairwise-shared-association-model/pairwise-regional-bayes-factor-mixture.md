# Pairwise regional Bayes-factor mixture for shared genetic influences

Partition the genome into $M$ approximately independent blocks and let $D$ be the GWAS summary statistics (effect estimates and standard errors) of two traits, with a correction for the correlation of the statistics induced by overlapping samples. Each block follows one of five models: $0$, no variant affecting either trait; $1$, a variant affecting trait 1 only; $2$, a variant affecting trait 2 only; $3$, one variant affecting both traits; $4$, two distinct variants, one for each trait. With prior probabilities $\Theta=(\Pi_0,\dots,\Pi_4)$, $\sum_j\Pi_j=1$, and regional Bayes factors $\mathrm{RBF}_i(j)$ measuring the support for model $j$ against model $0$ in block $i$, the log-likelihood is

$$\ell(\Theta\mid D)=\sum_{i=1}^M\ln\Big(\Pi_0+\sum_{j=1}^4\Pi_j\,\mathrm{RBF}_i(j)\Big),$$

and the posterior probability of model $j$ in block $i$ is

$$P(j\mid D_i)=\frac{\Pi_j\,\mathrm{RBF}_i(j)}{\Pi_0+\sum_{k=1}^4\Pi_k\,\mathrm{RBF}_i(k)}.$$

The priors are fitted genome-wide (penalised, i.e. maximum a posteriori), and $\hat\Pi_3$ estimates the proportion of blocks that detectably influence both traits.

## Depends on

- [The five colocalization hypotheses](../../bayesian-fine-mapping-and-colocalization/coloc-hypothesis.md)

## Expansion

Blocks are independent, so the likelihood is a product over blocks of a five-component mixture whose component likelihoods, divided by the null likelihood, are the regional Bayes factors. Estimating the mixing weights across the whole genome replaces the fixed per-locus priors of single-locus colocalization by empirical-Bayes priors specific to each trait pair. $\hat\Pi_3$ depends on power, so it is the share of detectable shared loci, not a genetic correlation, and models 3 and 4 are hard to separate when the two causal variants are in strong linkage disequilibrium.

## Sources

- J. K. Pickrell et al., "Detection and interpretation of shared genetic influences on 42 human traits", Nat. Genet. 48 (2016), 709–717, section "Identification of genetic variants that influence pairs of traits" and Figure 1, <https://doi.org/10.1038/ng.3570>, PMCID PMC5207801.
