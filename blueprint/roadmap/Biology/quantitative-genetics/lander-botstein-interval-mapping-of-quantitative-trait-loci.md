# Interval mapping of quantitative trait loci (Lander–Botstein)

Lander and Botstein (1989) introduce interval mapping, which exploits a complete genetic linkage map of codominant markers by adapting the LOD-score analysis of human genetics to estimate the location and phenotypic effect of quantitative trait loci (QTLs). In a backcross, consider a putative QTL between flanking markers $M_1$ and $M_2$ at recombination fractions $r_1$ from $M_1$ and $r_2$ from $M_2$, and let $r_{12}$ be the recombination fraction between the markers. With no interference, recombination in the two subintervals is independent, so $r_{12} = r_1 + r_2 - 2 r_1 r_2$, and given the flanking marker genotypes each individual's QTL genotype is one of the two backcross genotypes with conditional probabilities that are exact functions of $(r_1, r_2, r_{12})$: for a recombinant marker class the two genotypes have probabilities $r_1(1 - r_2)/r_{12}$ and $(1 - r_1) r_2/r_{12}$, and for a nonrecombinant class $r_1 r_2/(1 - r_{12})$ and $(1 - r_1)(1 - r_2)/(1 - r_{12})$. With a normal phenotype with genotype-specific means and common variance, the likelihood is therefore a product of two-component normal mixtures with known weights, and the LOD score at each position is the log-likelihood ratio of the mixture model maximized over the effect against the model without a QTL, scanned along the interval.

## Expansion

1. The model: the backcross, codominant marker genotypes, the recombination fractions, and the no-interference relation.
2. The conditional QTL genotype probabilities given the four flanking-marker classes, by Bayes' rule.
3. The mixture likelihood, its maximization, and the LOD profile along the interval.
4. The genome-wide significance threshold of the source, and selective genotyping, as separate statements.

## Sources

- E. S. Lander and D. Botstein, Mapping Mendelian factors underlying quantitative traits using RFLP linkage maps, Genetics 121 (1989), 185–199, abstract. <https://doi.org/10.1093/genetics/121.1.185>
