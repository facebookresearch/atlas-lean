---
article_id: af_e20cdc613157412c911d2aaa
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pow_pow_modEq_one_of_modEq_one
---

# Pow pow mod Eq one of mod Eq one

Lifting a congruence to one: if `a ≡ 1 [MOD p]` for any natural modulus `p` (not
necessarily prime), then `a ^ (p ^ n) ≡ 1 [MOD p ^ (n + 1)]` for every `n`. It is the `Nat.ModEq`
form of `dvd_sub_pow_of_dvd_sub`; `prime_power_lifting_modEq_one` is the source-shaped form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimePowerLifting](../../../../../sources/v2/MathlibExt.md)
