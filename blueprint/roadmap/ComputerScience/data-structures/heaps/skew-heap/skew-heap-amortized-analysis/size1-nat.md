# Size1 Nat

Isabelle's nat-valued `size1`: `size1 Leaf = 1`,
`size1 (Node l _ r) = size1 l + size1 r` (book Ch. 4 `|t|₁`).
Defined by the same recursion as in Isabelle, not as `size t + 1`.
