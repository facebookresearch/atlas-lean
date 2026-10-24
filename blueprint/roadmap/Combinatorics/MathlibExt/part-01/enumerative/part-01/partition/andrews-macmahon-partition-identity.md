---
article_id: af_428e0f8ada30736a76744a0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.andrews_macmahon_partition_identity
---

# Andrews Mac Mahon Partition

Andrews' generalization of MacMahon's identity: partitions of `n` whose
odd-multiplicity parts occur at least `2 * r + 1` times are equinumerous
with partitions of `n` whose odd parts are congruent to `2 * r + 1`
modulo `4 * r + 2`.

Provenance: Beaullah Mugwangwavari and Darlison Nyirenda, "A Note on the
Andrews-Ericksson-Petrov-Romick Bijection for MacMahon's Partition Theorem",
Journal of Integer Sequences 24 (2021), Article 21.5.6, Theorem `andthm`
(Andrews' generalization), source lines 113–115,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Nyirenda/nyir26.tex>.
The paper attributes the result to Andrews. At `r = 1` this recovers MacMahon's
partition theorem (no part occurring exactly once corresponds to parts even or
`3 mod 6`).

Proof: The generating-function route factors both sides through the even-part product and applies
Euler's odd/distinct identity, `Nat.Partition.card_odds_eq_card_distincts`, after substituting
`X ↦ X ^ (2 * r + 1)`; the source is Andrews' theorem as quoted in Mugwangwavari and Nyirenda.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.AndrewsMacMahonPartition](../../../../../../../sources/v2/MathlibExt.md)
