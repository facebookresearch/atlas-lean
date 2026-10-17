---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le_quarter_of_carmichael
---

# Card nonwitnesses le quarter of carmichael

The non-witnesses of a Carmichael number number at most `(n - 1) / 4`: with three pairwise
coprime factors `n₁ n₂ n₃ = n`, the units `w₁ ≡ v (mod n₁)` and `w₂ ≡ v (mod n₂)` (both `≡ 1`
modulo the other factors) give four distinct cosets of the subgroup that holds the
non-witnesses.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Coprime of witness eq false](coprime-of-witness-eq-false.md)
- [Two Adic Split](../miller-rabin/two-adic-split.md)
- [Witness](../miller-rabin/witness.md)
- [Witness eq false imp](witness-eq-false-imp.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
