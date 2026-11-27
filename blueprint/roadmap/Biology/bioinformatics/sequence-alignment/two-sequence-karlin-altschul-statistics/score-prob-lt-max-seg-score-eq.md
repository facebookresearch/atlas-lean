# For lattice scores, exceeding t means reaching the next lattice point

Let `h > 0`, let `q` and `f` be real weights and scores on a finite alphabet with every score
`f a` in the lattice `hℤ`, and let `L` be a natural number. For every real `t`, the
[score probability](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-prob.md) of
`{M_L > t}` equals that of `{M_L ≥ t⁺}`, where `M_L` is the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
scores of `L` letters and `t⁺ = (⌊t / h⌋ + 1) h` is the [lattice point above](lattice-above.md) `t`.
So the tail depends on `t` only through `⌊t / h⌋`, which is why the
[lattice tail hypothesis](one-sequence-lattice-tail.md) is stated at `t⁺`. When `q` is a
probability vector these are probabilities for `L` independent letters of law `q`.
