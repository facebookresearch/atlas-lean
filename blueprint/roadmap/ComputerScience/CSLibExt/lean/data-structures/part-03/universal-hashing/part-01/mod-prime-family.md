---
article_id: af_d58b855cb1939f2c37e55ed8
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.UniversalHashing.modPrimeFamily
---

# Mod Prime Family

The mod-prime family as a `Finset` of distinct functions. The universality result
below is proved for the indexed family `modPrimeHashes`, matching the `p * (p - 1)`
count of indices in CLRS; the image here can be smaller, since distinct index pairs
may agree as functions after the final reduction modulo `m`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Mod Prime Index](mod-prime-index.md)
- [Mod Prime Hashes](mod-prime-hashes.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing](../../../../../../../../sources/v2/CSLibExt.md)
