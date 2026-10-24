---
article_id: af_00ee2317cd8e670a11c56638
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.partitions_two_distant_eq_polarized
---

# Two Distant Polarized

Partitions with 2-distant parts equal polarized partitions.

A partition has 2-distant parts when it lies in `Dₙ²`, i.e. its parts are distinct
and any two parts differ by at least 2 (source lines 98–105).
A polarized partition has 1-distant (distinct) parts and every even part,
if there are any, is greater than twice the number of odd parts
(source lines 112–121); for all-odd partitions the even-part condition holds
vacuously, per the intended reading at source line 121.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.TwoDistantPolarized](../../../../../../../sources/v2/MathlibExt.md)
- Ivica Martinjak and Dragutin Svrtan, "New Identities for the Polarized Partitions and Partitions with d-Distant Parts," Journal of Integer Sequences 17 (2014), Article 14.11.4, Theorem 1 (label `Thm1`), lines 150–155, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Martinjak/mart3.tex>.
