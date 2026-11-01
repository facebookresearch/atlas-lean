---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.infinite_thirdOrderRecurrence_with_infinite_not_isSum
---

# Infinite third Order Recurrence with infinite not is Sum

There are infinitely many degree-three linear homogeneous
recurrence sequences of positive integers taking each positive
integer value only finitely often, each having infinitely many
terms that are not a sum of two prime powers. Degree three is
encoded using Mathlib's `LinearRecurrence` API: `fun n => (s n : ℤ)`
is a solution of an order-three recurrence whose coefficient of the
oldest term (`c 0`) is nonzero, but is not a solution of any
order-two recurrence. The positivity and fiber-finiteness
conditions exclude degenerate families such as the constant
negative sequences, which would otherwise satisfy the conclusion
for unrelated reasons (every term below `2` is nonrepresentable).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ThirdOrderPrimePowersWanted](../../../../../sources/v2/WantedExt.md)
- Baczkowski and Keener, *Third-Order Recurrence Sequences with Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal of Integer Sequences 29 (2026), Article 26.2.3, Corollary 1 (`jis-2026-26.2.3-cor-1`).
