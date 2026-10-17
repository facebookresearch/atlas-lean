---
article_id: af_8a61381e679ec5784e469651
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LruCache.mem_put_entries_iff_of_not_full
---

# Mem put entries iff of not full

When `put` evicts nothing, because the cache is not full or the key replaces an
existing binding, the stored entries are characterized exactly: the new binding together
with every previously stored binding for a different key, values unchanged.

## Depends on

- [Lru Cache](../part-01/lru-cache.md)
- [Keys](../part-01/keys.md)
- [Put](../part-01/put.md)
- [Size](../part-01/size.md)

## Proof depends on

- [Erase Key](../part-01/erase-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
