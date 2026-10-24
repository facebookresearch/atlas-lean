---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Int.mul_wilsonQuotient
---

# Mul wilson Quotient

Exact recovery: `p * W(p) = (p-1)! + 1` for a prime `p`.

This is the `ℤ`-form of the identity `(p-1)! = -1 + p * w_p` used in
Avitabile–Mattarei 2308.16034, `AH.tex` ll. 315–321. By Wilson's theorem the
division in `wilsonQuotient` is exact, so multiplying back recovers the numerator.

## Depends on

- [Wilson Quotient](wilson-quotient.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.WilsonQuotient](../../../../../sources/v2/MathlibExt.md)
