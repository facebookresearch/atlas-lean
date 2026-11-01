---
article_id: af_e0a173cfeede8f75a5972ec8
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.fubiniNumber
---

# Fubini Number

Fubini number (ordered Bell number) sequence `F : Nat → Nat`, including `n = 0`.

Concept `jis_sem_e1177ff556038d65c81b8a4b`; source statements
`jis_b26251532a8ea8d30aa79dc5` (Fubini numbers count weak orderings of `n`
elements with `n ∈ ℕ₀`), `jis_0874746b31275e17727c6370` (ordered Bell /
Fubini number as the cardinality of set compositions, i.e. ordered set
partitions), `jis_3e6dba4b03dc26402e017ca1`, `jis_5f1e2c9fcad751f6300d9e68`
(Stirling-transform relations between factorials and Fubini numbers).

`F n` counts weak orderings, equivalently ordered set partitions, of an
`n`-element set, formalized through the source Stirling-transform identity
using `Nat.stirlingSecond` and `Nat.factorial` directly.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.FubiniNumber](../../../../../../../sources/v2/MathlibExt.md)
