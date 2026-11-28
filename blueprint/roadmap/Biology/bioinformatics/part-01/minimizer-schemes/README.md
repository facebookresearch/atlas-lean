# Minimizer schemes

Read mappers, assemblers and metagenomic classifiers index a sequence by a sparse sample of its $k$-mers. A minimizer (winnowing) scheme picks, in every window of $w$ consecutive $k$-mers, the smallest one under a fixed order, so any two strings sharing a window share a sampled $k$-mer; other local methods (syncmers, word-based rules) decide from a bounded window too. The cost of a scheme is its density, the expected fraction of positions sampled. The theory relates density to charged contexts and universal hitting sets of the de Bruijn graph, fixes when density $O(1/w)$ is achievable, gives constructions that beat the random-order density $2/(w+1)$, tunes orders to a fixed sequence, and describes the conservation of selected $k$-mers under mutation and the bias of estimators computed on minimizer sketches.

- [Local k-mer selection methods and their densities](local-k-mer-selection-methods-and-their-densities.md)
- [Density of random minimizers via charged contexts](random-minimizer-density-and-charged-contexts.md)
- [Charged contexts and the energy of a random minimizer](charged-contexts-and-the-energy-of-a-random-minimizer.md)
- [Universal sets and asymptotically optimal minimizer density](universal-sets-and-asymptotically-optimal-minimizer-density.md)
- [When minimizers can reach density O(1/w)](asymptotic-optimality-condition-for-minimizers.md)
- [Density limit of minimizer schemes for large windows](density-limit-of-minimizer-schemes-for-large-windows.md)
- [Lower bound on the density of forward schemes](lower-bound-on-the-density-of-forward-schemes.md)
- [Density of minimizers ordered by a universal hitting set](density-of-minimizers-ordered-by-a-universal-hitting-set.md)
- [The Miniception minimizer construction](the-miniception.md)
- [Polar sets and the link-energy density bound](polar-sets-and-the-link-energy-density-bound.md)
- [Conservation of selected k-mers under point mutation](conservation-of-selected-k-mers-under-point-mutation.md)
- [Bias and inconsistency of the minimizer Jaccard estimator](bias-and-inconsistency-of-the-minimizer-jaccard-estimator.md)
