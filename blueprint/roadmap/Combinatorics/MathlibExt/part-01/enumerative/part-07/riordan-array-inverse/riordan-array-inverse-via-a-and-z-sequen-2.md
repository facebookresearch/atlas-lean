---
article_id: af_1a5f1512d44cb189c4639972
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.riordan_array_inverse_via_a_and_z_sequences
---

# Riordan array inverse via a and z sequences

Riordan array inverse from the A-sequence and Z-sequence generating functions.

`fInv` is the compositional inverse of `f`; `A` and `Z` are the generating functions
of the A-sequence and Z-sequence, with `f = X * subst f A` and
`g = d00 / (1 - X * subst f Z)`.
It follows from `riordan_array_inverse_via_a_and_z_sequences_general`; the hypothesis
`hcomp_right` is unused and keeps the source's shape.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Riordan array inverse via a and z sequences general](riordan-array-inverse-via-a-and-z-sequen.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.RiordanArrayInverse](../../../../../../../sources/v2/MathlibExt.md)
- Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays and Associated Integer Sequences," Journal of Integer Sequences 13 (2010), Article 10.9.4, Lemma (label `Lemma`), lines 280-283, <https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex>. The paper attributes this formula to Luzon.
