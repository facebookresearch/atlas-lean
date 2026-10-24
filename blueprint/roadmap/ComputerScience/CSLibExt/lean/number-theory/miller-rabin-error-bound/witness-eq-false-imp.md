---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.witness_eq_false_imp
---

# Witness eq false imp

CLRS's description of a non-witness: with `n - 1 = 2^t u`, either `a^u ≡ 1` or
`a^(2^i u) ≡ -1` for some `i < t`.

## Depends on

- [Two Adic Split](../miller-rabin/two-adic-split.md)
- [Witness](../miller-rabin/witness.md)

## Proof depends on

- [Witness Loop](../miller-rabin/witness-loop.md)
- [Witness Loop eq false imp](witness-loop-eq-false-imp.md)
- [Modular Exponentiation](../modular-exponentiation/modular-exponentiation.md)
- [Modular Exponentiation correct](../modular-exponentiation/modular-exponentiation-correct.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
