# Odd Length Normalized Kernel Shortening

Odd-length normalized kernel shortening via cyclic same-side rotation.

For a normalized alternating word `L` of odd length at least three whose
boundary-block product lies in `ker toStableE`, the two endpoints lie on the
same side. Rotating the last block to the front creates an adjacent same-side
pair, normalizing strictly shortens the word while preserving the alternating
chain, the kernel condition, and the exact noncommutative conjugacy
`prod Lnorm = lastBlock * prod L * lastBlock⁻¹`. Membership of the normalized
product in `torusCocycleSubgroup` transports back to the original product
via centrality. Handles empty/singleton/length-two exclusion through
`3 ≤ L.length`; `n = 0` remains valid. No even-length, pivot, or Matsumoto
claim.
