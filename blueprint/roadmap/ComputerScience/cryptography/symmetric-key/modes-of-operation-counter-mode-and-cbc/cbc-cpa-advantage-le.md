# CBC mode, the PRP step

Let the key space `K`, the block group `X` (with decidable equality) and the
adversary coins `R` be finite and nonempty, and let `E` be a block cipher. For
every CPA adversary against CBC mode with `ℓ`-block messages whose coins are
uniform on `R` and which makes at most `q` encryption queries, the CPA
advantage is at most the PRP advantage against `E` of the reduction
`cbcReduction`, plus the deviation from `1/2` of the success probability of
the same reduction against a uniformly random permutation.
