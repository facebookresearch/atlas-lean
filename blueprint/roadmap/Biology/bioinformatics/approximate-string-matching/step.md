# One column update of the bit-vector algorithm

For a pattern of length `m`, the update
takes the state `(Pv, Mv, score)` and the match mask `Eq` of the next text character, where
`Eq`, `Pv` and `Mv` are `m`-bit vectors, that is naturals below `2^m`. The update does not reduce
these inputs, so wider ones are outside its contract. With `mask = 2^m - 1` and `¬x = mask ⊕ x`:
`Xv = Eq ∨ Mv`, `Xh = ((((Eq ∧ Pv) + Pv) ∧ mask) ⊕ Pv) ∨ Eq`, `Ph = Mv ∨ ¬(Xh ∨ Pv)`,
`Mh = Pv ∧ Xh`; the score increases by one if bit `m - 1` of `Ph` is set and otherwise
decreases by one if bit `m - 1` of `Mh` is set; then `Ph` and `Mh` are shifted left by one
(without carry-in, since `C[0, j] = 0`) and reduced modulo `2^m`, and the new state is
`Pv' = Mh ∨ ¬(Xv ∨ Ph)`, `Mv' = Ph ∧ Xv`, again `m`-bit vectors.
