# Markov random field priors for pathway GWAS

Bayesian gene-level association analysis in which the unknown association labels of the genes in a pathway receive a nearest-neighbour Gibbs (Ising-type) prior on the pathway graph, so that interacting genes tend to share association status. The posterior is again a Markov random field, with auto-logistic full conditionals that drive Gibbs sampling, iterated conditional modes and posterior-probability decision rules.

- [Auto-logistic conditionals of a pathway Markov random field](auto-logistic-conditionals-of-a-pathway-markov-random-field.md)
