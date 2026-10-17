---
article_id: af_1b962de2d3277b54cb61b4f7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.macmahon_multiplicity_one_free
---

# Mac Mahon Multiplicity One Free

MacMahon's partition theorem: for every `n`, the number of partitions of `n`
with no part occurring exactly once equals the number of partitions of `n` all of
whose parts are even or congruent to `3` modulo `6`.

The left side counts `p : Nat.Partition n` satisfying
`Multiset.count m p.parts ≠ 1` for every part `m ∈ p.parts`. The right side is
the existing `Nat.Partition.restricted` finset for the per-part predicate
`m % 2 = 0 ∨ m % 6 = 3`.

Provenance: Beaullah Mugwangwavari and Darlison Nyirenda, "A Note on the
Andrews-Ericksson-Petrov-Romick Bijection for MacMahon's Partition Theorem",
Journal of Integer Sequences 24 (2021), Article 21.5.6, Theorem `MacMahon`,
source lines 88–97 with the displayed statement at lines 91–93,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Nyirenda/nyir26.tex>.
The paper attributes the theorem to P. A. MacMahon, *Combinatory Analysis*,
Vol. 2 (1916).

Scope: the source fixes `n ≥ 1`. The statement here is over all `n : ℕ`; at
`n = 0` both filtered sets consist solely of the empty partition, so including
`n = 0` is a proved-by-definition endpoint extension rather than a claim copied
from the source.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.MacMahonMultiplicityOneFree](../../../../../../../sources/v2/MathlibExt.md)
