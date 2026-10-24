---
article_id: af_645679617b6a5a37fa12486d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.compositions_parts_one_two_three_eq_canonical_tribonacci
---

# Compositions parts one two three eq canonical tribonacci

This is the canonical-sequence form (OEIS A000073 indexing) of the theorem above.

Proof: Specialize `compositions_parts_one_two_three_eq_tribonacci` to
`T k = tribonacci (k + 1)`, whose initial values and recurrence hold by definition.

## Depends on

- [Tribonacci Sequence With Initial Values001](../../../../../../NumberTheory/MathlibExt/part-11/tribonacci.md)

## Proof depends on

- [Compositions parts one two three eq tribonacci](compositions-parts-one-two-three-eq-trib.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CompositionsTribonacci](../../../../../../../sources/v2/MathlibExt.md)
