---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le_of_carmichael
---

# Card nonwitnesses le of carmichael

CLRS Theorem 31.38, case 2: for a Carmichael number (Mathlib's `Nat.IsCarmichael`) the
non-witnesses lie in the proper subgroup `{x : x^(2^j u) = ±1}`.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Coprime of witness eq false](coprime-of-witness-eq-false.md)
- [Two Adic Split](../miller-rabin/two-adic-split.md)
- [Witness](../miller-rabin/witness.md)
- [Witness eq false imp](witness-eq-false-imp.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
