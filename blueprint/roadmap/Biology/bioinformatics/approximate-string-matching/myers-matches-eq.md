# Correctness of the bit-vector algorithm

For a nonempty pattern `P`, any text `T` and any threshold `k`, the positions reported by the
bit-vector algorithm are, in increasing order, exactly the text positions `1 ≤ j ≤ |T|` with
`dp P T |P| j ≤ k` (Myers 1999).

The source's algorithm rests on Lemma 1: since every vertical delta of the dynamic-programming
matrix lies in `{-1, 0, 1}`, a column is determined by its vertical deltas, which the bit vectors
`Pv` and `Mv` encode.

## Depends on

- [Dp](dp.md)
- [Myers Matches](myers-matches.md)

## Proof depends on

- [Deltas lie in `{-1, 0, 1}`](delta-mem.md)

## Sources

- G. Myers, "A fast bit-vector algorithm for approximate string matching based on dynamic
  programming", J. ACM 46(3) (1999) 395-415, Lemma 1 and the column-update algorithm.
