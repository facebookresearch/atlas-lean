# Elston–Stewart peeling for pedigree likelihoods

For a pedigree with a founder genotype law, Mendelian transmission from parents to children and phenotypes conditionally independent given genotypes, the likelihood is

$$L = \sum_{g} \prod_{\text{founders } f} P(g_f) \prod_{\text{non-founders } o} P(g_o \mid g_{m(o)}, g_{p(o)}) \prod_{i} P(x_i \mid g_i).$$

In a nuclear family the offspring are conditionally independent given the parental genotypes, so the sum over offspring genotypes factorizes and the cost grows linearly with the number of offspring. Elston and Stewart (1971) extended this to simple pedigrees (the distinction between simple and complex pedigrees is made precise by Lange and Elston 1975), in which every person is either related to someone in the previous generation or marries into the pedigree and there are no consanguineous marriages: starting at the bottom of the pedigree, each nuclear family is processed by fixing the genotype of one parent and summing over the spouse's and the offspring's genotypes, giving conditional probabilities $H(g)$ (with $H = 1$ for individuals without descendants), and after all nuclear families are processed the likelihood is the sum over founder genotypes $\sum_g P(x \mid g) H(g) P(g)$ (Elston and Stewart 1971). For a fixed finite genotype alphabet, processing a nuclear family with $m$ children costs order $m + 1$ (a bounded number of parental genotype pairs, each with $m$ offspring factors), so the total cost is linear in the number of people in the pedigree, equivalently in the number of parent–child incidences; it is linear in the number of nuclear families only when family sizes are bounded, since one family with $m$ children already has order $m$ observations to read. For jointly analyzed loci the genotype alphabet is the product of the per-locus alphabets, so the constant in this bound grows exponentially with the number of loci.

## Depends on

- [Pedigree](../../quantitative-genetics/pedigree-kinship-and-inbreeding/pedigree.md)
- [Mendel's law of segregation](../../population-genetics/hardy-weinberg-law/transmit.md)

## Expansion

1. The model: pedigrees as parent–child relations, simple (loop-free, non-consanguineous) pedigrees, genotype laws and penetrances.
2. The factorization of the joint law and the conditional independence of offspring given parents.
3. The recursive elimination over nuclear families from the bottom of the pedigree, and correctness of each step.
4. The cost bound for a fixed genotype alphabet, linear in the number of people (or parent–child incidences), the bound in the number of nuclear families under bounded family size, and the exponential growth in the number of loci.
5. Pedigrees with loops or consanguineous marriages (the complex pedigrees of Lange and Elston 1975), as a separate statement.

## Sources

- Original result: R. C. Elston and J. Stewart, A general model for the genetic analysis of pedigree data, Hum. Hered. 21 (1971), 523–542. <https://doi.org/10.1159/000152448>
- K. Lange and R. C. Elston, Extensions to pedigree analysis I. Likelihood calculations for simple and complex pedigrees, Hum. Hered. 25 (1975), 95–105. <https://doi.org/10.1159/000152714>
