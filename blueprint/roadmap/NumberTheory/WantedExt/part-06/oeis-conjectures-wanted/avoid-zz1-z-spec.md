---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.OeisConjecturesWanted.avoidZZ1Z_spec
---

# Theorem 3

**Theorem 3**: the numbers `f_k(n)` of words of
length `n` over a `k`-letter avoiding the pattern
`z, z+1, z` satisfy `f_k(0) = 1`, `f_k(1) = k`,
`f_k(2) = k^2`, and, for `n ≥ 3`,
`f_k(n) = k f_k(n-1) - f_k(n-2) + f_k(n-3)`. The
alphabet is nonempty (`k ≥ 1`); at `k = 0` the recurrence
would read `0 = 1` at `n = 3`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.OeisConjecturesWanted](../../../../../sources/v2/WantedExt.md)
- Sela Fried, "Proofs of Several Conjectures From the OEIS", Theorem 3.
