---
article_id: af_8c5d378e8d0074799aa56079
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.wittMultigradedValue
---

# Witt Multigraded Value

Witt's multigraded value `M(n₁, …, nᵣ)`: let `n` be the sum of all entries
of `degree` and `g` their finite gcd; `M` is `(1/n)` times the sum over
positive `d` dividing `g` of `μ(d)` times the multinomial coefficient for
`i ↦ degree i / d` (`ArithmeticFunction.moebius` and `Nat.multinomial`,
coerced into `ℚ`); the `n = 0` boundary is `0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Algebra.Lie.WittMultigradedValue](../../../../sources/v2/MathlibExt.md)
- Pieter Moree, *Convoluted Convolved Fibonacci Numbers*, Journal of Integer Sequences 7 (2004), Article 04.2.2, equations `witty`/`basaal`, lines 598–613 (Möbius inversion of the circular-word count; context *Circular words and Witt's dimension formula*, lines 574–597), <https://cs.uwaterloo.ca/journals/JIS/VOL7/Moree/moree12.tex>.
