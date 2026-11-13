# A PRP family is a PRF family

**A PRP family is a PRF family** (Katz and Lindell, Section 3.5.1): if every admissible
distinguisher family makes polynomially many queries and the birthday term
`collisionProb (X n) (p n)` is negligible for every polynomial `p` (e.g. `|X n| = 2 ^ n`), then
PRP security implies PRF security.
