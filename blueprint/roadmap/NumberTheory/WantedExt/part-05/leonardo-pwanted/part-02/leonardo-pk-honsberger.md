---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK_honsberger
---

# Theorem 13

**Theorem 13** (Honsberger-type identity, index
corrected): for positive `m, n`,
`ℒ_{p,k}(m)ℒ_{p,k}(n+1) + ∑_{i=1}^p ℒ_{p,k}(m-i)
ℒ_{p,k}(n-p+i) = (k+1)ℒ_{p,k}(m+n+1) -
k(ℒ_{p,k}(m+p) + ℒ_{p,k}(n+p+1)) + pk² + k`, with
`ℒ_{p,k}` at negative arguments read through the same
recurrence (here `leonardoPK` at truncated indices,
where the paper's values at negative arguments in
`[-p, -1]` are `-k`; the statement is stated with the
`ℤ`-extension `leonardoPKZ` below).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.LeonardoPWanted](../../../../../../sources/v2/WantedExt.md)
- "On Generalized Leonardo `p`-Numbers", Journal of Integer Sequences 27 (2024), Article 24.4.6, Theorem 13.
