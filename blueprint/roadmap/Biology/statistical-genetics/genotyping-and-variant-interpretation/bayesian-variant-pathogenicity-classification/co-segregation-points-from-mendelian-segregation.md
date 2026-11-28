# Co-segregation points from Mendelian segregation probabilities

Work in the [points-based Bayesian framework](points-based-bayesian-odds-of-pathogenicity.md) with base factor $c$. Suppose a family with a fully penetrant Mendelian disorder and established phase, and compare two hypotheses: the tested variant (or allele pair) is causal, or it is unlinked to the disease and segregates independently. For one relative whose genotype and phenotype agree with the causal hypothesis, the likelihood ratio is $1/q$, where $q$ is the probability of that agreement by chance under Mendelian segregation, so the relative contributes

$$x=\log_c\frac1q\ \text{points}.$$

With $c\approx2$ this gives the ClinGen co-segregation table (Table 3):

| Inheritance and relative | chance agreement $q$ | points per co-segregation |
|---|---|---|
| autosomal dominant, affected or unaffected relative | $1/2$ | $1.0$ |
| X-linked recessive, affected or unaffected male | $1/2$ | $1.0$ |
| autosomal recessive, affected sibling (inherits both parental alleles) | $1/4$ | $2.0$ |
| autosomal recessive, unaffected sibling (not homozygous for the pair) | $3/4$ | $0.4$ |

Points add over independent meioses, unaffected relatives count only under full penetrance, parents used to establish phase do not count, and the total locus evidence is capped at $+5$ points per allele. Under locus homogeneity, once phenotype specificity already implicates the locus with near certainty, co-segregation adds essentially no further evidence; with locus heterogeneity, evidence against one locus is evidence for the others.

## Depends on

- [Points-based Bayesian odds of pathogenicity](points-based-bayesian-odds-of-pathogenicity.md)

## Expansion

For a dominant disorder each child of a heterozygous parent inherits the variant with probability $1/2$, so a relative whose carrier status matches their phenotype has chance probability $1/2$ and likelihood ratio $2$. For a recessive disorder with known parental phase, a sibling receives both parental variant alleles with probability $1/4$ (ratio $4$, $\log_{2.08}4=1.89\approx2$) and avoids being doubly affected with probability $3/4$ (ratio $4/3$, $\log_{2.08}(4/3)=0.39\approx0.4$). Penetrance below one breaks the unaffected-relative calculation, which is why those relatives are excluded then.

## Sources

- L. G. Biesecker, A. B. Byrne, S. M. Harrison et al., *ClinGen guidance for use of the PP1/BS4 co-segregation and PP4 phenotype specificity criteria for sequence variants*, The American Journal of Human Genetics 111 (2024), 24–38, <https://doi.org/10.1016/j.ajhg.2023.11.009> (PMCID: PMC10806742). Table 3 and its footnotes, the worked autosomal-recessive and X-linked examples, and the discussion of locus homogeneity and heterogeneity (Results). The segregation probabilities in the Expansion are standard Mendelian calculations that reproduce the table.
