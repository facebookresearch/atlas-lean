---
article_id: af_5ade3453c65d33cdb89f7a7b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.aronsonTransform_existsUnique
---

# Aronson Transform exists Unique

The Aronson transform of a strictly increasing sequence with infinite
complement exists uniquely: for a strictly increasing `β` of integers
`≥ n₀` whose complement above `n₀` is infinite, there is a unique strictly
increasing `α` with values `≥ n₀` given by the greedy rule that each `n`
is in the range of `α` exactly when the next value of `α` is in the range
of `β`, taking the smallest consistent value at each step.

It follows from `aronsonTransform_existsUnique_general`; the hypothesis `hβ_lower` is unused
and keeps the source's shape.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Aronson Transform exists Unique general](aronson-transform-exists-unique-general.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Sequences.AronsonTransform](../../../../../../sources/v2/MathlibExt.md)
- Benoit Cloitre, N. J. A. Sloane, and Matthew J. Vandermast, "Numerical Analogues of Aronson's Sequence," Journal of Integer Sequences 6 (2003), Article 03.2.2, Theorem `ThAT1`, lines 782–784 (transform defined lines 761–780), https://cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.tex
