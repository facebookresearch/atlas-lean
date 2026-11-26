# Evaluation of taxonomic classifiers against reference databases

Benchmarking a marker-gene taxonomic classifier on the database it was trained from overstates accuracy, because every query then has an exact match. Cross-validation over a reference database fixes this only after the target labels are corrected: a query whose taxon is absent from the training fold cannot be classified to that taxon, and the correct answer is instead the lowest common ancestor shared with the training set.

- [Lowest-common-ancestor truncation of expected taxonomy](lowest-common-ancestor-truncation-of-expected-taxonomy.md)
