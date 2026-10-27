---
article_id: af_1951e1bc5fcee306fca95d73
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LruCache.mem_get_entries_iff
---

# Mem get entries iff

`get` preserves exactly the stored bindings: promotion reorders but neither adds,
removes, nor changes any entry.

## Depends on

- [Lru Cache](lru-cache.md)
- [Get](get.md)

## Proof depends on

- [Erase Key](erase-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LruCache](../../../../../../../../sources/v2/CSLibExt.md)
