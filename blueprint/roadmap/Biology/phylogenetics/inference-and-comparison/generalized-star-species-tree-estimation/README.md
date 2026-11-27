# Generalized STAR species-tree estimation

STAR infers a species tree from a sample of rooted gene-tree topologies by giving every gene tree a standard ultrametric metric determined by node depths, averaging the resulting distance matrices, and applying a distance method. Under the multispecies coalescent, any depth-based node numbering that is non-increasing from root to leaves yields a statistically consistent estimator of the species tree topology, the expected distances depend only on clade probabilities, and a seemingly natural descendant-count numbering fails.

- [Consistency of generalized STAR node numberings](consistency-of-generalized-star-node-numberings.md)
- [Clade probabilities determine expected STAR distances](clade-probabilities-determine-expected-star-distances.md)
