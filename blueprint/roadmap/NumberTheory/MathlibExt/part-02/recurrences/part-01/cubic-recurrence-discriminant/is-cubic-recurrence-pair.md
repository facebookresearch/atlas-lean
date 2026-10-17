---
article_id: af_fe83ff5d86e3087aa1787040
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsCubicRecurrencePair
---

# Is Cubic Recurrence Pair

A pair of integer sequences satisfying the source's explicit algebraic
definitions. The witnesses `γ₁, γ₂, γ₃` are the distinct nonunit parameters
whose product is one and whose associated `R * (γᵢ + γᵢ⁻¹)` values are the
three roots of the source cubic. The equations then determine every value of
`U` and `W`; the `U` equation is denominator-cleared and starts at `n = 1`,
while `U 0 = 0` is specified separately.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cubic Recurrence Root Condition](cubic-recurrence-root-condition.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.CubicRecurrenceDiscriminant](../../../../../../../sources/v2/MathlibExt.md)
