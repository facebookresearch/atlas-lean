---
article_id: af_bd2b1b450fbb8c00f948365a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: IsCyclotomicExtension.Rat.eq_bot_of_isUnramifiedIn_prime_pow
---

# Eq bot of is Unramified In prime pow

A subfield of a `p`-power cyclotomic extension that is unramified at `p`
is the bottom field.

This is the prime-power vanishing step of the N390 maximality argument
(`cyclotomic_ppow_unramified_le_bot` in the primary source). The exponent is
an arbitrary `e` and the ambient field an arbitrary number field `L`; the
source's `e = padicValNat p m` with `L = CyclotomicField m ℚ` is recovered
in the test file.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Unramified In of not dvd](is-unramified-in-of-not-dvd.md)
- [Is Unramified In mono](../../../part-02/unramified/is-unramified-in-mono.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.Cyclotomic.Unramified](../../../../../../../../sources/v2/MathlibExt.md)
