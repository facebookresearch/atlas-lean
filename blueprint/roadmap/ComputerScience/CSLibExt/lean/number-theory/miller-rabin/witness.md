---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.witness
---

# Witness

CLRS `WITNESS(a, n)`. For a base with `0 < a < n`, `true` proves `n` composite
(`not_prime_of_witness`); outside that range the answer carries no such guarantee (for example
`witness 2 2 = true`), as in CLRS, whose bases are drawn from `1, …, n - 1`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Two Adic Split](two-adic-split.md)
- [Witness Loop](witness-loop.md)
- [Modular Exponentiation](../modular-exponentiation/modular-exponentiation.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin](../../../../../../sources/v2/CSLibExt.md)
