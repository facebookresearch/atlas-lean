---
article_id: af_3cab8145fae165769ce451fb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.uspensky_no_partition_into_three_or_more_beatty_sequences
---

# Uspensky Beatty Partition

Uspensky's theorem on partitions into Beatty sequences: there exists no
partition of the positive integers into three or more Beatty sequences.

Beatty-sequence and partition conventions from the same source, lines 183–200:
`B_α = (⌊n/α⌋)` with `0 < α < 1`, `ℕ = {1, 2, ...}`, and a partition means
every element belongs to exactly one subset. The source statement carries no
irrationality hypothesis. The complement version (Theorem B*, lines 260–263)
is a source-declared equivalent and is not stated separately.
Proves `Wanted` entry `uspensky_no_partition_into_three_or_more_beatty_sequences`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Beatty.UspenskyBeattyPartition](../../../../../sources/v2/MathlibExt.md)
- A. J. Hildebrand, Xiaomin Li, Junxian Li, and Yun Xie, *Almost Beatty Partitions*, Journal of Integer Sequences 22 (2019), Article 19.4.6, Theorem B (Uspensky's theorem), lines 234–236, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Hildebrand/hilde2.tex>; first proved by Uspensky in 1927 (lines 238–244).
