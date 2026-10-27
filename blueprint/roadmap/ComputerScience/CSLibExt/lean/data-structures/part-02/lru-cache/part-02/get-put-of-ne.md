---
article_id: af_ee06660fa8d86e7f0505864c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LruCache.get_put_of_ne
---

# Get put of ne

Looking up a different key after a `put` that evicts nothing returns exactly what the
lookup returned before the `put`: surviving bindings keep their values.

## Depends on

- [Lru Cache](../part-01/lru-cache.md)
- [Get](../part-01/get.md)
- [Keys](../part-01/keys.md)
- [Put](../part-01/put.md)
- [Size](../part-01/size.md)

## Proof depends on

- [Get hit](../part-01/get-hit.md)
- [Get miss](../part-01/get-miss.md)
- [Mem put entries iff of not full](mem-put-entries-iff-of-not-full.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
