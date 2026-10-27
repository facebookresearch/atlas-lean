---
article_id: af_0f97364d4428549e58df641c
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.dusart_pi_asymptotic_expansion
---

# Dusart Pi Asymptotic Expansion Wanted

Dusart asymptotic expansion for `π(x)` with explicit error: for
`x ≥ 4e9`, `π(x) = x / log x * (1 + 1 / log x + 2 / (log x)^2 + E)`
with `|E| ≤ 7.32 / (log x)^3`, and `π` as `Nat.primeCounting ⌊x⌋₊`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.DusartPiAsymptoticExpansionWanted](../../../../../../sources/v2/WantedExt.md)
- Pierre Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.1.
