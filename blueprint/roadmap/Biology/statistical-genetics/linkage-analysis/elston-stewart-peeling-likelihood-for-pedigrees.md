# Elston–Stewart peeling for pedigree likelihoods

For a pedigree with a founder genotype law, Mendelian transmission from parents to children and phenotypes conditionally independent given genotypes, the likelihood is
$$L = \sum_{g} \prod_{\text{founders } f} P(g_f) \prod_{\text{non-founders } o} P(g_o \mid g_{m(o)}, g_{p(o)}) \prod_{i} P(x_i \mid g_i).$$
In a nuclear family the offspring are conditionally independent given the parental genotypes, so the sum over offspring genotypes factorizes and the cost grows linearly with the number of offspring. Elston and Stewart (1971) extended this to special pedigrees, in which every person is either related to someone in the previous generation or marries into the pedigree and there are no consanguineous marriages: starting at the bottom of the pedigree, each nuclear family is processed by fixing the genotype of one parent and summing over the spouse's and the offspring's genotypes, giving conditional probabilities $H(g)$ (with $H = 1$ for individuals without descendants), and after all nuclear families are processed the likelihood is the sum over founder genotypes $\sum_g P(x \mid g) H(g) P(g)$ (Biostatistics 666 notes). For a fixed finite genotype alphabet each step sums over a bounded number of genotype pairs, so the total cost is linear in the number of nuclear families, while it grows exponentially with the number of jointly analyzed loci.

## Expansion

1. The model: pedigrees as parent–child relations, special (loop-free, non-consanguineous) pedigrees, genotype laws and penetrances.
2. The factorization of the joint law and the conditional independence of offspring given parents.
3. The recursive elimination over nuclear families from the bottom of the pedigree, and correctness of each step.
4. The cost bound for a fixed genotype alphabet, and its exponential growth in the number of loci.
5. Pedigrees with loops or consanguineous marriages, as a separate statement.

## Sources

- Likelihood calculation in large families, lecture notes, Biostatistics 666, University of Michigan. <https://genome.sph.umich.edu/w/images/b/bd/666.24.pdf>
- Original result: R. C. Elston and J. Stewart, A general model for the genetic analysis of pedigree data, Hum. Hered. 21 (1971), 523–542. <https://doi.org/10.1159/000152448> The peeling recursion over nuclear families of special pedigrees follows the Biostatistics 666 notes.
