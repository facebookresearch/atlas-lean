# A pseudorandom permutation is a pseudorandom function

**A pseudorandom permutation is a pseudorandom function** (Katz and Lindell, Section 3.5.1),
in concrete form: for a distinguisher making at most `q` queries, its PRF advantage against
`fun k => F k` is at most its PRP advantage against `F` plus the collision probability of `q`
uniform samples from `X` (at most `q (q - 1) / (2 |X|)`, `collisionProb_le`).
