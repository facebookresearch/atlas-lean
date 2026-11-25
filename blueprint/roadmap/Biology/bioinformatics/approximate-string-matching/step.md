# Step

One column update of the bit-vector algorithm for a pattern of length `m`, on the state
`(Pv, Mv, score)` and the match mask `Eq` of the next text character (all bit vectors reduced
modulo `2^m`, and `mask = 2^m - 1`):
`Xv = Eq ∨ Mv`, `Xh = (((Eq ∧ Pv) + Pv) ∧ mask) ⊕ Pv) ∨ Eq`, `Ph = Mv ∨ ¬(Xh ∨ Pv)`,
`Mh = Pv ∧ Xh`; the score increases by one if bit `m - 1` of `Ph` is set and otherwise
decreases by one if bit `m - 1` of `Mh` is set; then `Ph` and `Mh` are shifted left by one
(without carry-in, since `C[0, j] = 0`), and the new state is `Pv' = Mh ∨ ¬(Xv ∨ Ph)`,
`Mv' = Ph ∧ Xv`.
