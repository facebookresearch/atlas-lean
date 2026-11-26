# Full-hash collisions are block-level collisions

Let the chaining values `S` have decidable equality and the coins `R` be
finite and nonempty, with `0 < n` and `maxLen + L + n ≤ n * maxBlocks`. For
every adversary `A : R → List Bool × List Bool`, the probability that `A`
finds a collision of the full hash among messages shorter than `maxLen` is at
most the probability that `blockAdversary n L A` finds a block-level hash
collision among block lists shorter than `maxBlocks`.
