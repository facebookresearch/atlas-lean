---
article_id: af_0d7b4edf4445e35b4ee42971
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsCloitreSelfDescribing
---

# Is Cloitre Self Describing

Self-description: run-sums are twice the original sequence.

There is a run boundary `b` with `2 * s n =` run-sum over block `n` for every
`n`, avoiding truncated `Nat` division (e.g. run-sums
`2, 2, 4, 2, 2, 2, 2, 4, …` halve to `1, 1, 2, 1, 1, 1, 1, 2, …`).
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Run Boundary](is-run-boundary.md)
- [Cloitre Run Sum](cloitre-run-sum.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.CloitreSequence](../../../../../../sources/v2/MathlibExt.md)
