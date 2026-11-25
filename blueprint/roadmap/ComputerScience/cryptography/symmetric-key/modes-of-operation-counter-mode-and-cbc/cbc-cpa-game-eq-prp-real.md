# The real world of the CBC reduction

Let the key space `K`, the block group `X` (with decidable equality) and the
adversary coins `R` be finite and nonempty, and let `E` be a block cipher. For
every CPA adversary against CBC mode whose coins are uniform on `R` and which
makes at most `q` encryption queries, the CPA game of CBC mode equals the
real-world PRP game of `E` against the reduction `cbcReduction`: with the
oracle `F_k`, the reduction runs the CPA game exactly.
