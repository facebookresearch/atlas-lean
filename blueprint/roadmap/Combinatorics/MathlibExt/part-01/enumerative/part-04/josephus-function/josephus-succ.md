---
article_id: af_804a4082fe6c00f167a0c6c0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.josephus_succ
---

# Josephus succ

One-based Euler recurrence (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `euler_recurrence`): for `n ≥ 1`,
`J_k(n+1) = ((J_k(n) + k - 1) mod (n+1)) + 1`. The hypotheses `_hk` and `_hn`
record the source domain `k ≥ 2`, `n ≥ 1` and are unused by the proof.

## Depends on

- [Josephus](josephus.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.JosephusFunction](../../../../../../../sources/v2/MathlibExt.md)
