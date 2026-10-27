---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le_quarter_of_pow_ne_one
---

# Card nonwitnesses le quarter of pow ne one

The non-witnesses of an odd `n` that is neither prime nor a prime power, and that has a
unit `z` with `z^(n-1) ≠ 1`, number at most `(n - 1) / 4`: with `w` as in case 2, the units `w`,
`z`, `w z` and `w⁻¹ z` lie outside the subgroup that holds the non-witnesses, because
`w^(2m) = 1` and `z^(2m) ≠ 1`.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Coprime of witness eq false](coprime-of-witness-eq-false.md)
- [Two Adic Split](../miller-rabin/two-adic-split.md)
- [Witness](../miller-rabin/witness.md)
- [Witness eq false imp](witness-eq-false-imp.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
