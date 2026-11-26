# Similarity-aware data splitting

Splitting biomolecular datasets (proteins, small molecules, sequences, drug-target pairs) into training, validation and test folds so that similar entities do not straddle folds, while respecting fold sizes and class proportions. The exact problem is NP-hard; a cluster-level integer linear program gives a constant-size surrogate.

- [NP-hardness of leakage-minimizing data splitting](np-hardness-of-leakage-minimizing-data-splitting.md)
- [Integer linear program for cluster-level data splitting](integer-linear-program-for-cluster-level-data-splitting.md)
