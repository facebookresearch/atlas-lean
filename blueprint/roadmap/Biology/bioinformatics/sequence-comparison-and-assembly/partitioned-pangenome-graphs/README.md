# Partitioned pangenome graphs

The gene families of a prokaryotic species can be split into a persistent genome (present in almost all strains), a cloud genome (rare families) and one or more shell genomes (intermediate frequency). A statistical partition treats each family's presence/absence pattern across genomes as a draw from a multivariate Bernoulli mixture, and smooths the assignment with a hidden Markov random field on the pangenome graph, whose nodes are gene families and whose edges join families that are genomic neighbours.

- [Multivariate Bernoulli mixture of gene presence/absence patterns](multivariate-bernoulli-mixture-of-gene-presence-absence-patterns.md)
- [Hidden Markov random field on a pangenome graph](hidden-markov-random-field-on-a-pangenome-graph.md)
