# Coalescent with recombination: ancestral-material state space and generator

Let the loci be $1, \dots, L$, with recombination rate $\rho_i/2$ per lineage between adjacent loci $i$ and $i + 1$, and total $\rho = \sum_i \rho_i$ ($\rho = 2Mr$ in units of $M$ gene copies; $4Nr$ in the diploid convention). A state is a finite multiset of lineages, each carrying a nonempty set of ancestral material: pairs (locus, subset of the sample) recording, at each locus, the sample copies to which the lineage is ancestral. The dynamics are:

- each pair of lineages coalesces at rate $1$, and their ancestral material merges;
- a lineage whose material lies on both sides of the breakpoint between loci $i$ and $i + 1$ splits there at rate $\rho_i/2$ into the lineages carrying its material on either side.

The conventions are fixed explicitly. Under the reduced convention, material at a locus is deleted once that locus reaches its most recent common ancestor, and loci with no material left are dropped. The process then ends in the empty state at $\tau_{\mathrm{red}} = \max_x T_{\mathrm{MRCA}}(x)$, not at a single lineage. Here $\rho \ge 0$.

For two loci and a sample of two this is [the two-locus coalescent](two-locus-rate.md) on its six states.

## Proof depends on

- [Rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md)
- [Transition function of a rate matrix is stochastic](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition-mem-row-stochastic.md)

## Expansion

1. The generator is a rate matrix: its rows sum to $0$.
2. Projection to $L = 2$ and $n = 2$ recovers [the rate matrix of the two-locus coalescent](two-locus-rate.md) exactly.
3. For $\rho = 0$ the generator lumps to [the rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md).
4. For $n = 2$ and $\rho = 0$, under the reduced convention the number of lineages jumps from $2$ to $0$ at the coalescence: there is no state with one lineage.

## Sources

- R. R. Hudson, Properties of a neutral allele model with intragenic recombination, *Theor. Popul. Biol.* 23 (1983), 183–201, <https://pubmed.ncbi.nlm.nih.gov/6612631/> (intragenic recombination model).
- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (the ancestral recombination graph).
- R. C. Griffiths, The two-locus ancestral graph, in *Selected Proceedings of the Sheffield Symposium on Applied Probability*, IMS Lecture Notes 18 (1991), 100–117 (two-locus ancestral graph).
