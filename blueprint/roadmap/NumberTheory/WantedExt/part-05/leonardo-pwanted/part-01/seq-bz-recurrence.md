---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LeonardoPWanted.seqBZ_recurrence
---

# Proposition 7

**Proposition 7**(ii): for `p ≥ 2` and `n ≥ 1`,
`B_p(n)` is `B_p(n-1) + B_p(n-p-1)` plus `1` if
`n ≡ 1 (mod p)`, minus `1` if `n ≡ 2 (mod p)`, else `0`;
the congruences are read as `n % p = c % p`, so at
`p = 2` the increment is `+1` for odd `n` and `-1` for
even `n` (e.g. `B_2(2) - B_2(1) - B_2(-1) = -1`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.LeonardoPWanted](../../../../../../sources/v2/WantedExt.md)
- "On Generalized Leonardo `p`-Numbers", Journal of Integer Sequences 27 (2024), Article 24.4.6, Proposition 7.
