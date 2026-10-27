---
article_id: af_8c01d3611802511c1c7c9907
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.binet_closed_form_second_order
---

# Binet Closed Form

Generalized Binet closed form: a sequence satisfying
`u (n + 2) = P * u (n + 1) - Q * u n` over a field, whose characteristic
roots `α ≠ β` both satisfy `z ^ 2 - P * z + Q = 0`, is given by
`u n = ((u 1 - β * u 0) * α ^ n - (u 1 - α * u 0) * β ^ n) / (α - β)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.BinetClosedForm](../../../../sources/v2/MathlibExt.md)
- Hongshen Chua, "A Study of Second-Order Linear Recurrence Sequences via Continuants," Journal of Integer Sequences 26 (2023), Article 23.8.8, Theorem [Binet's formula] (label Th:Binet_Formula), lines 270–274, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Chua2/chua13.tex>. Proves `Wanted` entry `binet_closed_form_second_order`.
