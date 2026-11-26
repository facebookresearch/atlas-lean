# Pairwise ancestral process of an autotetraploid Wright–Fisher population

Consider a monoecious population of $N$ autotetraploid individuals with tetrasomic inheritance, nonoverlapping generations and no recombination or double reduction: an individual carrying four distinct alleles at the locus produces each of the $\binom{4}{2} = 6$ gamete types with equal probability, and each of the $N$ offspring is formed by two gametes drawn uniformly with replacement from the gametes of the parental generation, so that an offspring is selfed with probability $1/N$.

Track two distinct genetic lineages backwards in time through the three states $1$ (the two lineages lie in the same individual), $2$ (they lie in different individuals) and $3$ (they have coalesced). The one-generation transition matrix is

$$P = \begin{pmatrix} \tfrac{1}{3} + \tfrac{1}{2N} & \tfrac{2}{3}\left(1 - \tfrac{1}{N}\right) & \tfrac{1}{6N} \\[2pt] \tfrac{3}{4N} & 1 - \tfrac{1}{N} & \tfrac{1}{4N} \\[2pt] 0 & 0 & 1 \end{pmatrix},$$

with state $3$ absorbing. In particular a within-individual pair coalesces in one generation with probability $P_{1,3} = 1/(6N)$, and a between-individual pair with probability $P_{2,3} = 1/(4N)$.

Samples of chromosomes from a tetraploid are therefore **not** exchangeable: the one-generation coalescence probability depends on whether the two lineages sit in the same individual.

## Depends on

- [Finite-state Markov chain with a given transition matrix](../../../../Probability/markov-chains/finite-markov-chains/is-finite-markov-chain.md)

## Expansion

For the within-individual pair, coalescence in the previous generation requires that the two lineages came from different gametes (probability $2/3$), that those gametes came from the same parent (probability $1/N$) and that they trace to the same parental chromosome (probability $1/4$), giving $P_{1,3} = (2/3)(1/N)(1/4) = 1/(6N)$; this reproduces Wright's factor $5/6$ for the decay of the proportion of unlike pairs of genes under complete selfing in autotetraploids. For the between-individual pair one sums over all patterns of shared ancestry that can make the two lineages identical by descent, which after simplification gives $P_{2,3} = 1/(4N)$. The remaining entries follow from the same conditioning, and each row sums to one. Two lineages that came from the same gamete cannot coalesce in the immediately preceding generation when double reduction is excluded, which is exactly the failure of exchangeability.

## Sources

- B. Arnold, K. Bomblies, J. Wakeley, "Extending coalescent theory to autotetraploids", *Genetics* 192 (2012), 195–204, <https://doi.org/10.1534/genetics.112.140582> (PMC3430536). Theory, "Sample size of two chromosomes".
