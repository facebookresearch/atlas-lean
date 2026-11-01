---
article_id: af_e8d30b7980bfd06edfab4e83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.digital_binomial_theorem_general
---

# Digital binomial theorem general

Digital binomial theorem over a commutative semiring: `(x + y) ^ s(n)` is the sum of
`x ^ s(m) * y ^ s(n - m)` over the `m ≤ n` with `s(m) + s(n - m) = s(n)`, where `s` is
`binDigitSum`.

## Depends on

- [Bin Digit Sum](bin-digit-sum.md)

## Proof depends on

- [Bin Digit Sum two mul](bin-digit-sum-two-mul.md)
- [Bin Digit Sum two mul add one](bin-digit-sum-two-mul-add-one.md)
- [Bin Digit Sum zero](bin-digit-sum-zero.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.DigitalBinomialTheorem](../../../../../../../sources/v2/MathlibExt.md)
