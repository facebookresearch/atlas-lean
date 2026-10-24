---
article_id: af_24e24d1a2847da43cab641ff
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.steuerwald_three_perfect_exponents
---

# Steuerwald three perfect exponents

Steuerwald's theorem on 3-perfect numbers: if `N = 2 ^ a * 3 ^ b * m` with
`a, b ≥ 1`, `Nat.Coprime 6 m`, and `ArithmeticFunction.sigma 1 N = 3 * N`,
then `(a = 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ b = 1)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.SteuerwaldThreePerfect](../../../../../sources/v2/MathlibExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL25/Almeida/almeida9.tex, lines 210-219, text SHA cfc728d5cbd8ccc703d9bfda34db0857b0ba43251881d2ba3a73b45503209f75, file SHA 47d90eedae7bb76cfb0845e93958ce17dff96d5d9a65ca310917738a33a1eea6.
