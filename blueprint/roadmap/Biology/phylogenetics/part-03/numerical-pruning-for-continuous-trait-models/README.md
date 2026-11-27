# Numerical pruning for continuous trait models

Likelihood computation for quantitative traits evolving along a phylogeny when the model is not Gaussian at the tips, for example Wright–Felsenstein threshold models in which a Brownian liability is observed only as a binary character. Felsenstein's discrete-state pruning recursion is applied to continuous states by storing partial likelihoods on a grid and replacing each integral by a quadrature rule, which keeps the cost linear in the number of taxa.

- [Quadrature pruning for the phylogenetic threshold model](quadrature-pruning-for-the-phylogenetic-threshold-model.md)
