---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.card_nonwitnesses_le_quarter_of_prime_pow
---

# Card nonwitnesses le quarter of prime pow

The non-witnesses of an odd prime power `p^k` with `k ≥ 2` number at most `p - 1 ≤ (p^k - 1)/4`:
they satisfy `a^(p^k - 1) ≡ 1`, and two of them that agree modulo `p` agree modulo `p^k`, since
their quotient `x` has `x^(p^(k-1)) = 1` (lifting the exponent) and `x^(p^k - 1) = 1` with
coprime exponents.

## Depends on

- [Nonwitnesses](nonwitnesses.md)

## Proof depends on

- [Coprime of witness eq false](coprime-of-witness-eq-false.md)
- [Witness](../miller-rabin/witness.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound](../../../../../../sources/v2/CSLibExt.md)
