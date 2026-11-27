# Expected cross value for mate selection

Genomic mate selection ranks candidate parent pairs by what their progeny's gametes are expected to carry. Modelling which parental haplotype transmits each locus as a two-state Markov chain along the chromosome (switch probability = recombination frequency) gives closed-form marginal transmission probabilities, and the expected number of desirable alleles in a grandchild gamete is then linear in the parents' genotype matrices, so the best pair can be found by integer linear programming.

- [Inheritance distribution and the expected cross value](inheritance-distribution-and-the-expected-cross-value.md)
