# Piling-up lemma

Matsui's piling-up lemma: for `n ≥ 1` and distributions `p i` on `Bool`, `i :
Fin n`, if the bits are drawn independently, the probability that their
exclusive or is `false` equals `1/2 + 2 ^ (n - 1) * ∏ i, bias (p i)`, where
`bias q = Pr_q[false] - 1/2`.
