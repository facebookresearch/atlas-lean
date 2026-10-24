---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le_of_pow_ne_one
---

# Card nonwitnesses le of pow ne one

If some unit `x` has `x^(n-1) ≢ 1`, the non-witnesses lie in the proper subgroup
`{y : y^(n-1) = 1}`.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Coprime of witness eq false](coprime-of-witness-eq-false.md)
- [Witness](../miller-rabin/witness.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
