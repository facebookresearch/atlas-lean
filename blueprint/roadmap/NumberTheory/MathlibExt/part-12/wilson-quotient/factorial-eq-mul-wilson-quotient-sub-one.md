---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Int.factorial_eq_mul_wilsonQuotient_sub_one
---

# Factorial eq mul wilson Quotient sub one

Factorial form of the recovery identity: `(p-1)! = p * W(p) - 1`.

Equivalent to `mul_wilsonQuotient` with the `+1` moved, matching the
display `(p-1)! = -1 + p * w_p` from Avitabile–Mattarei `AH.tex` ll. 315–321.

## Depends on

- [Wilson Quotient](wilson-quotient.md)

## Proof depends on

- [Mul wilson Quotient](mul-wilson-quotient.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.WilsonQuotient](../../../../../sources/v2/MathlibExt.md)
