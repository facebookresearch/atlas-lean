---
article_id: af_3b603059ab0d9dcf7eab1300
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.josephus
---

# Josephus

Josephus survivor function `J_k` (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clauses `domain`, `meaning`): the one-based
position of the sole survivor when every `k`th person is eliminated from a
circle of `n` people. Defined by structural recursion on the population: the
value at `0` is `0` purely as the recursion anchor (public theorems retain the
source domain `2 ≤ k` and `1 ≤ n`); successors use the one-based Euler
recurrence.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.JosephusFunction](../../../../../../../sources/v2/MathlibExt.md)
