---
article_id: af_ffc50e5378668a57c2f5193a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LruCache.evicted_is_least_recent
---

# Evicted is least recent

The key evicted by inserting a new key is the least recently used one: if a stored key `k`
disappears after putting a key `k'` that was not in the cache, the cache was full and `k` was
the last (least recent) key.

## Depends on

- [Lru Cache](../part-01/lru-cache.md)
- [Keys](../part-01/keys.md)
- [Put](../part-01/put.md)
- [Size](../part-01/size.md)

## Proof depends on

- [Erase Key](../part-01/erase-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
