---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.FOL.consistent_sUnion_of_isChain
---

# Consistent s Union of is Chain

The union of a nonempty chain of consistent sets is consistent: a refutation uses finitely
many hypotheses, which lie in one member (Mathlib's
`DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion`).

## Depends on

- [Consistent](consistent.md)

## Proof depends on

- [Natural deduction](../natural-deduction/derivable.md)
- [Provable](../natural-deduction/provable.md)

## Sources

- [CSLibExt, CSLibExt.Logics.FirstOrder.Consistency](../../../../../sources/v2/CSLibExt.md)
