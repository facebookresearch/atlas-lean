# On two states the GTR matrix is the equal-input generator

On the two states `0` and `1`, let `π` be real base frequencies with `π 0 + π 1 = 1` and `s` a
symmetric real `2 × 2` matrix, and write `Q` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. Then `Q` is the
[equal-input generator](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-sticky-equal-input-kernel-on-a-finite-state/equal-input-rate.md)
with rate `s 0 1`: `Q = s 0 1 · (𝟙 πᵀ - I)`, with entries `s 0 1 · (π j - [i = j])`, where `𝟙 πᵀ` is
the matrix whose rows all equal `π` and `[i = j]` is `1` if `i = j` and `0` otherwise.
