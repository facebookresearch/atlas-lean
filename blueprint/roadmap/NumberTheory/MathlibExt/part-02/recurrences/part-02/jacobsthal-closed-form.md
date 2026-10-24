---
article_id: af_d375a1e4cf6f72b7e2fe0d6e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.jacobsthal_closedForm
---

# Jacobsthal Closed Form

The closed form for the Jacobsthal sequence with initial values
`J 0 = 1` and `J 1 = 1`.

The explicit formula is the source's Theorem; the source cites
A. Tucker, "Applied Combinatorics," 3rd edition.
It follows from `binet_closed_form_second_order` with `P = 1`, `Q = -2`,
`α = 2` and `β = -1`.
Proves `Wanted` entry `jacobsthal_closedForm`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Binet Closed Form](../../../part-03/binet-closed-form-second-order.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.JacobsthalClosedForm](../../../../../../sources/v2/MathlibExt.md)
- Darrin D. Frey and James A. Sellers, "Jacobsthal Numbers and Alternating Sign Matrices," Journal of Integer Sequences 3 (2000), Article 00.2.3, recurrence (label jacrecur) with initial values, lines 260–266, and Theorem, equation (Eq4a), lines 329–335, https://cs.uwaterloo.ca/journals/JIS/VOL3/SELLERS/sellers.tex
