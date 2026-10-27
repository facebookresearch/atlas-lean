---
article_id: af_59e269ff64fb444db6cd9b61
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ncard_regular_eq_sum_totient_unitaryDivisors
---

# Ncard regular eq sum totient unitary Divisors

Morgado's formula over `Nat.unitaryDivisors`: for `0 < n`, the number of regular residues
`m : ZMod n` (those for which `m ^ 2 * x = m` is solvable) is `∑ d ∈ n.unitaryDivisors, φ d`.
`morgado_card_regular_modulo` is the source-shaped form.

## Depends on

- [Unitary Divisors](../../../part-11/unitary-divisor/unitary-divisors.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.MorgadoRegularResidues](../../../../../../sources/v2/MathlibExt.md)
