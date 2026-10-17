---
article_id: af_af423dfa8cd2a904df7ba3b9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.engel_bell_log_convexity
---

# Engel Bell Log Convexity

Engel's log-convexity inequality for Bell numbers, Eq. (E2).

Horst Alzer, "On Engel's Inequality for Bell Numbers,"
Journal of Integer Sequences 22 (2019).

Stable concept id: `jis_grounded_0ea6ed8edd46a1ad43f4d963`.

Scope: this is the complete selected non-strict theorem as stated in Eq. (E2);
it is not Alzer's later strict refinement nor the series identity.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bell Turan Identity](../part-01/bell-turan-identity.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.EngelBellLogConvexity](../../../../../../sources/v2/MathlibExt.md)
- <https://cs.uwaterloo.ca/journals/JIS/VOL22/Alzer/alzer6.tex>, lines 79--104, where `B_n` is defined as the Bell number and Eq. (E2) states `B_n^2 ≤ B_{n-1} B_{n+1}` for every integer `n ≥ 1`. Source file SHA-256: `03a0712f6a473227541845886072d039e644d950ee6f591a456b1cffcd1b9f46`. The source attributes this inequality to K. Engel, "On the average rank of an element in a filter of the partition lattice," J. Combin. Theory Ser. A 65 (1994), 67--78.
