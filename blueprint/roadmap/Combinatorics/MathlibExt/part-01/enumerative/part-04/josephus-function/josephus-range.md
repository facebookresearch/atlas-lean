---
article_id: af_7e28ff88beb88a69d30090f9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.josephus_range
---

# Josephus range

Range `J_k(n) ∈ [[1, n]]` (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `range`): for every `n ≥ 1`,
`1 ≤ J_k(n)` and `J_k(n) ≤ n`. The hypothesis `_hk` records the source domain
`k ≥ 2` and is unused by the proof.

## Depends on

- [Josephus](josephus.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.JosephusFunction](../../../../../../../sources/v2/MathlibExt.md)
