---
article_id: af_236af88cf122a2f78ae2d271
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LruCache.get_put
---

# Get put

Looking up a key immediately after putting it returns the stored value, provided the capacity
is positive so the new entry is not itself evicted.

## Depends on

- [Lru Cache](lru-cache.md)
- [Get](get.md)
- [Put](put.md)

## Proof depends on

- [Erase Key](erase-key.md)
- [Get hit](get-hit.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
