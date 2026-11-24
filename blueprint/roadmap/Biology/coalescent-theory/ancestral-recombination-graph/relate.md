# Genealogy estimation by Relate

Relate (Speidel, Forest, Shi and Myers 2019, Methods) estimates genome-wide genealogies in three steps. First, at each focal site a hidden Markov model similar to that of Li and Stephens, modified to distinguish ancestral and derived states, gives for each haplotype $i$ the probabilities of copying from each other haplotype $j$; rescaled log probabilities form a position-specific distance matrix $d$, whose entry $(i, j)$ converges to the number of mutations derived in $i$ and ancestral in $j$ when there is no recombination. Second, a hierarchical clustering merges at each step a pair of clades that, according to the rows of $d$, coalesce with each other before coalescing with any other clade; if the data are consistent with a binary tree under the infinite-sites model such a pair always exists, and with no recombination the procedure returns the correct topology. Mutations are then mapped to the branch whose descendants are exactly the carriers of the derived allele, where possible. Third, branch lengths are estimated by a Metropolis–Hastings Markov chain Monte Carlo algorithm with a coalescent prior for a single panmictic population, and the effective population size, defined as the inverse coalescence rate, is re-estimated from the branch lengths in an alternating loop.

## Expansion

1. The ancestral-derived copying model and the position-specific distance matrix.
2. The clustering step: existence of a mergeable pair for data consistent with a binary tree under infinite sites, and recovery of the true topology without recombination.
3. Mapping of mutations to branches and the compatibility of each mapped mutation with exactly one branch.
4. The posterior of branch times given a topology and the mapped mutations under the coalescent prior, and a Metropolis–Hastings sampler with that target.
5. The alternating estimation of coalescence rates and branch lengths, as a separate procedure without a convergence guarantee.

## Sources

- L. Speidel, M. Forest, S. Shi and S. R. Myers, A method for genome-wide genealogy estimation for thousands of samples, Nat. Genet. 51 (2019), 1321–1329, Methods: "Calculating position specific distance matrices", "Tree builder", "Mapping mutations to branches and estimating branch lengths" and "Estimating coalescence rates through time". <https://doi.org/10.1038/s41588-019-0484-x>
