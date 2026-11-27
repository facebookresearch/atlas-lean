# Othello hashing for k-mer indexing

Othello is a minimal-perfect-hashing-style data structure that stores a map from a key set to small integer categories in two arrays combined by XOR, with constant-time queries. Used as a k-mer index over many sequencing experiments, it never errs on stored k-mers, and a query for an absent ("alien") k-mer is recognized as absent with probability bounded away from zero.

- [Alien k-mer rejection probability of an Othello index](alien-k-mer-rejection-probability-of-an-othello-index.md)
