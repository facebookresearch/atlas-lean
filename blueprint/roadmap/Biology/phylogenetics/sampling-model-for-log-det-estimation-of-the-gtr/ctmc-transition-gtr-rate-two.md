# Closed-form two-state transition function

On the two states `0` and `1`, let `π` be real base frequencies with `π 0 + π 1 = 1` and `s` a
symmetric real `2 × 2` matrix, and write `Q` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. Then for every real `t` and all states `i`, `j`,
`exp (t · Q) i j = e · [i = j] + (1 - e) · π j` with `e = exp (-(s 0 1 · t))`, where `[i = j]` is
`1` if `i = j` and `0` otherwise.
