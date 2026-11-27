# Statistics derived from ancestral recombination graphs

Quantities computed from an estimated genealogy are conditional expectations or estimators given that genealogy. The expected genetic relatedness matrix (eGRM) used for tree-based quantitative-trait mapping by Link et al. (2023) is the expectation of the genetic relatedness matrix when mutations are placed on the ancestral recombination graph as a Poisson process; it is the weighted average of the single-locus relatedness matrices defined by the branches of the graph, with weights proportional to the expected numbers of mutations on the branches, and it is tested for association with a phenotype by restricted maximum likelihood in a variance-components model. Edge and Coop (2019) estimate the historical time course $Z(t)$ of a population-mean polygenic score as $\hat Z(t) = 2\sum_{i=1}^{k} \beta_i \hat p_i(t)$ (their equation (2)), with $\beta_i$ the effect sizes and $\hat p_i(t)$ allele-frequency estimates read from the coalescent tree at locus $i$ by three estimators (proportion of lineages, waiting time, lineages remaining); for independent loci $\mathrm{Var}[\hat Z(t)] = 4\sum_i \beta_i^2 \mathrm{Var}[\hat p_i(t)]$ (equation (3)). How errors in the inferred genealogy propagate into these quantities is a separate question.

## Depends on

- [Site and branch statistics of a tree sequence and their duality](../../site-and-branch-statistics-duality/site-and-branch-statistics.md)

## Expansion

1. The eGRM as a branch statistic of the tree sequence and its identity with the conditional expectation of the genotype relatedness matrix under Poisson mutation.
2. The variance-components test of the local eGRM against a phenotype.
3. The three estimators of a historical allele frequency from a coalescent tree, and the polygenic-score estimator with its variance for independent loci.
4. Sensitivity of each derived quantity to errors in the estimated genealogy, as a separate statement.

## Sources

- V. Link et al., Tree-based QTL mapping with expected local genetic relatedness matrices, Am. J. Hum. Genet. 110 (2023), 2077–2091, Subjects and methods (the eGRM definition), Introduction and Fig. 1. <https://doi.org/10.1016/j.ajhg.2023.10.017>
- M. D. Edge and G. Coop, Reconstructing the history of polygenic scores using coalescent trees, Genetics 211 (2019), 235–262, equations (2), (3) and Fig. 2. <https://doi.org/10.1534/genetics.118.301687>
