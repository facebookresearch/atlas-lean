# Minimizer sampling of k-mers

Read mappers, assemblers and metagenomic classifiers index a sequence by a sparse sample of its $k$-mers. A minimizer scheme picks, in every window of $w$ consecutive $k$-mers, the smallest one under a fixed order, so any two strings sharing a window share a sampled $k$-mer. The cost of the scheme is its density, the expected fraction of positions sampled; the theory relates density to charged contexts and universal hitting sets, fixes when density $O(1/w)$ is achievable, and gives constructions that beat the random-order density $2/(w+1)$.

- [Density of random minimizers via charged contexts](random-minimizer-density-and-charged-contexts.md)
- [When minimizers can reach density O(1/w)](asymptotic-optimality-condition-for-minimizers.md)
- [The Miniception minimizer construction](the-miniception.md)
