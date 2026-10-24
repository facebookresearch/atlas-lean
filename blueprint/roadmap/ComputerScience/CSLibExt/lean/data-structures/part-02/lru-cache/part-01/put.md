---
article_id: af_9b52c177c54485db1626b7bc
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LruCache.put
---

# Put

Inserts or updates the binding for `k` at the front of the cache, evicting the least recently
used entries if the cache would exceed its capacity.

## Depends on

- [Lru Cache](lru-cache.md)

## Proof depends on

- [Erase Key](erase-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
