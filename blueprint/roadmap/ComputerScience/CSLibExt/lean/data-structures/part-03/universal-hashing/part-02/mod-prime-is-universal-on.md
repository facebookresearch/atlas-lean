---
article_id: af_73aeec5cbf21dea1c6ee4f01
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.UniversalHashing.modPrime_isUniversalOn
---

# Mod Prime is Universal On

Universality of the mod-prime family (CLRS Theorem 11.5): the indexed family
`modPrimeHashes` over all `(a, b)` with `a ≠ 0` is universal. A uniformly random
index therefore collides on any two distinct keys with probability at most `1 / m`.

## Depends on

- [Is Universal On](../part-01/is-universal-on.md)
- [Mod Prime Index](../part-01/mod-prime-index.md)
- [Mod Prime Hashes](../part-01/mod-prime-hashes.md)

## Proof depends on

- [Mod Prime Index card](mod-prime-index-card.md)
- [Mod Prime collision mul le](mod-prime-collision-mul-le.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing](../../../../../../../../sources/v2/CSLibExt.md)
