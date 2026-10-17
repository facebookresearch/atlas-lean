---
article_id: af_4cbbd067ab180c7412114c03
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.lucas_binet_formulas
---

# Lucas binet formulas

Binet formulas for the Lucas sequences `U(P, Q)` and `V(P, Q)`.

Distinct-root case (`alpha ≠ beta`): with `alpha + beta = P` and
`alpha * beta = Q`, one has `Uₙ = (alpha ^ n - beta ^ n) / (alpha - beta)`
and `Vₙ = alpha ^ n + beta ^ n` for all `n`.

Double-root case (`beta = alpha`): then `P = 2 * alpha` and `Q = alpha ^ 2`,
and the formulas degenerate to `Uₙ = n * alpha ^ (n - 1)` and
`Vₙ = 2 * alpha ^ n` for all `n`. The natural subtraction in `n - 1` is
harmless at `n = 0` because the coefficient `(n : K)` is zero there.

Provenance: Christian Ballot, "A Further Generalization of a Congruence of
Wolstenholme", Journal of Integer Sequences 15 (2012), Article 12.8.6,
sequence definitions and formulas at lines 274–289,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Ballot/ballot4.tex
complete-source SHA-256
`b96be332c67702b765cf4d73089ecb09c1e544c95afec737b8ff1445e4bffa17`;
normalized lines 274–289 SHA-256
`a1f6755e5072c434c537d1e8c874715fad642cdc2f3ecae191f676022d222a5e`;
normalized formula lines 283–289 SHA-256
`955c225b2d2be3f81e25044e2179816a66f1923c22b4b40bf21c9cdef276e0c9`.

## Depends on

- [Lucas Sequence Params](../../../../part-07/lucas-sequence/lucas-sequence-params.md)
- [Lucas U](../../../../part-07/lucas-sequence/lucas-u.md)
- [Lucas V](../../../../part-07/lucas-sequence/lucas-v.md)

## Proof depends on

- [Lucas binet formulas of field](lucas-binet-formulas-of-field.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.LucasBinetFormula](../../../../../../../sources/v2/MathlibExt.md)
