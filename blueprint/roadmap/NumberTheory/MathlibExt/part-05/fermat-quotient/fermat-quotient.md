---
article_id: af_957709c9d193774f61f9934e
declaration: def
origin: cited
statement: formalized
lean: Int.fermatQuotient
---

# Fermat Quotient

Fermat quotient `q_p(a) = (a ^ (p - 1) - 1) / p` for prime `p` and `a`
coprime to `p`. Integrality follows from `Int.prime_dvd_pow_sub_one`.
Proof arguments `_hp` and `_ha` are retained to enforce the domain
restriction to prime moduli and coprime integers, though the computed
value is independent of witnesses.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.FermatQuotient](../../../../../sources/v2/MathlibExt.md)
