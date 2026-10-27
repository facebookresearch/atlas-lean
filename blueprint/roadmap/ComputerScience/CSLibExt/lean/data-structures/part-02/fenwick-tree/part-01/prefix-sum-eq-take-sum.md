---
article_id: af_2252a5653363cf0ebd7239f3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.prefixSum_eq_take_sum
---

# Prefix Sum eq take sum

For every `k`, including values past the end, `prefixSum` agrees with the
sum of the corresponding `List.take` of the represented array.

## Depends on

- [Fenwick Tree](fenwick-tree.md)
- [Valid](valid.md)
- [Prefix Sum](prefix-sum.md)

## Proof depends on

- [Block Sum](block-sum.md)
- [Lowbit](lowbit.md)
- [Lowbit le](lowbit-le.md)
- [Lowbit pos](lowbit-pos.md)
- [Size](size.md)
- [Size eq length of valid](size-eq-length-of-valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
