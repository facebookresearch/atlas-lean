---
article_id: af_89a686114a3f18adb2a32a04
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.GeneralizedThueMorse.block
---

# Block

Finite blocks `Aₙ` of the `(L, k, κ)`-TM sequence
(concept `jis_sem_12ac243c6e8826ae73e194e0`, statement `jis_099e0392547ec836b0b913d1`):
`A₀` is the one-letter word `a₀`, and `Aₙ₊₁` concatenates `Aₙ` with each
whole-word cyclic shift `f^{κ(j,n)}(Aₙ)` for `j = 1, …, k-1`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Shift Word](shift-word.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence](../../../../../../../sources/v2/MathlibExt.md)
