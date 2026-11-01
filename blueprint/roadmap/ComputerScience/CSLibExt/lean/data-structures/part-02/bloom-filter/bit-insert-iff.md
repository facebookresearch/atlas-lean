---
article_id: af_c3654251854d8af552ba26db
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BloomFilter.bit_insert_iff
---

# Bit insert iff

Bit-set characterization of insertion: after inserting `x`, bit `i` is set exactly when it was
already set or some hash function sends `x` to `i`.

## Depends on

- [Bloom Filter](bloom-filter.md)
- [Insert](insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BloomFilter](../../../../../../../sources/v2/CSLibExt.md)
