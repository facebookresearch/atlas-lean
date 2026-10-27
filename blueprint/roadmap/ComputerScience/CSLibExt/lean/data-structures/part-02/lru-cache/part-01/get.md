---
article_id: af_0f721aac9f3c624dcf7eac62
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LruCache.get
---

# Get

Looks up `k`. On a hit, returns the stored value and the cache with that entry promoted to the
front; on a miss, returns `none` and the unchanged cache.

## Depends on

- [Lru Cache](lru-cache.md)

## Proof depends on

- [Erase Key](erase-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
