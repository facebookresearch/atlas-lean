---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.witness_of_pow_ne_one
---

# Witness of pow ne one

Every Fermat witness is a Miller–Rabin witness: if `a^(n-1) ≢ 1 (mod n)` then `WITNESS(a, n)`
returns `true`.

## Depends on

- [Witness](witness.md)

## Proof depends on

- [Two Adic Split](two-adic-split.md)
- [Witness Loop](witness-loop.md)
- [Witness Loop eq true](witness-loop-eq-true.md)
- [Modular Exponentiation](../modular-exponentiation/modular-exponentiation.md)
- [Modular Exponentiation correct](../modular-exponentiation/modular-exponentiation-correct.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin](../../../../../../sources/v2/CSLibExt.md)
