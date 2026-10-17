---
article_id: af_dc479f81ddcd9eeb7fdacc81
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.UniversalHashing.modPrime_collision_mul_le
---

# Mod Prime collision mul le

The key counting lemma (CLRS Theorem 11.5, counting step): for distinct keys `x ≠ y`,
the number of indices `(a, b)`, `a ≠ 0`, for which `h_{a,b}` collides on `x` and `y`,
multiplied by `m`, is at most `p * (p - 1)`, the total number of indices. The
bijection `pairEquiv` identifies colliding indices with the colliding pairs counted
in `collidingPairs_mul_le`.

## Depends on

- [Mod Prime Index](../part-01/mod-prime-index.md)
- [Mod Prime Hashes](../part-01/mod-prime-hashes.md)

## Proof depends on

- [Mod Prime Hash](../part-01/mod-prime-hash.md)
- [Mod Prime Hash eq iff](../part-01/mod-prime-hash-eq-iff.md)
- [Pair Equiv](../part-01/pair-equiv.md)
- [Pair Equiv apply fst](../part-01/pair-equiv-apply-fst.md)
- [Pair Map](../part-01/pair-map.md)
- [Pair Map fst ne snd](../part-01/pair-map-fst-ne-snd.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing](../../../../../../../../sources/v2/CSLibExt.md)
