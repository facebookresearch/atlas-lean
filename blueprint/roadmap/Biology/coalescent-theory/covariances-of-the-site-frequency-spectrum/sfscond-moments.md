# Conditional moments of the site frequency spectrum given the genealogy

Given the
genealogy σ-algebra `m`, the counts `ξ i` (sites whose derived allele is carried by exactly `i`
sample copies) are independent Poisson variables with means `(θ / 2) L i`, where `L i` is the
total length of the branches subtending exactly `i` copies. Only the first two conditional
moments are recorded:

* `E[ξ_i | m] = (θ / 2) L_i`;
* `E[ξ_i ξ_j | m] = (θ / 2)² L_i L_j + δ_{ij} (θ / 2) L_i` (conditional covariance
  `δ_{ij} (θ / 2) L_i`: distinct size classes occupy disjoint sets of branches, so their
  mutation counts are conditionally independent; a Poisson count has variance equal to its
  mean),

together with square integrability of the counts and of the branch lengths.
