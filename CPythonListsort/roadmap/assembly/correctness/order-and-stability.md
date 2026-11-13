---
declaration: structure
origin: bridged
statement: formalized
lean: CPythonListsort.BoolStrictWeakOrder
---

# Boolean strict-weak-order specification

Define `BoolStrictWeakOrder lt` by reusing Mathlib's `IsStrictWeakOrder` for the
Prop-valued relation `fun a b => lt a b = true`. Define comparator equivalence
as mutual failure of strict comparison. The structure contains only order laws;
it must not contain sortedness, stability, or correctness conclusions.

## Depends on

- [Total Boolean comparator model](../../transcription/comparator-model.md)

## Sources

- [Top-level theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
- [Mathlib order prior art](../../../sources/mathlib-prior-art.md#order-assumptions)
