---
article_id: af_68ab0d3ad99c2060a4ef87bf
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: isBigO_abelSummatory_atTop
---

# Is Big O abel Summatory at Top

Under `A(n) = O(n ^ σ)` for arbitrary real `σ`, the summatory function
is `O(t ^ σ)` at infinity. The floor comparison goes through
`Asymptotics.isEquivalent_nat_floor.rpow` applied to the symmetric
equivalence, so the nonnegativity hypothesis falls on real casts of
naturals (always true) rather than on `σ`.

## Depends on

- [Abel Partial Sum](abel-partial-sum.md)
- [Abel Summatory](abel-summatory.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.LSeries.AbelContinuation](../../../../../../sources/v2/MathlibExt.md)
