---
article_id: af_62c981a17c2592d44c309ba7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.crank_nonneg_partition_count
---

# Crank Generating Function

Coefficient-wise form of the generating function for partitions with
non-negative crank: the number of partitions of `N` with crank `≥ 0` equals
`∑_n (-1)^n p(N - (n+1)n/2)`, the convolution of the partition numbers with
`(-1)^n` at the triangular numbers. The crank is the largest part when no
part equals `1`, else the number of parts exceeding the number of ones
minus the number of ones. The source notes this result is originally due
to Uncu. Verified at `N = 0..8`. Distinct from the same paper's quoted
Rogers–Ramanujan theorem.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.CrankGeneratingFunction](../../../../../../../sources/v2/MathlibExt.md)
- George E. Andrews and David Newman, "The Minimal Excludant in Integer Partitions," Journal of Integer Sequences 23 (2020), Article 20.2.3, Theorem (label Theorem1, equation 1.11), lines 161–165, https://cs.uwaterloo.ca/journals/JIS/VOL23/Andrews/andrews5.tex
