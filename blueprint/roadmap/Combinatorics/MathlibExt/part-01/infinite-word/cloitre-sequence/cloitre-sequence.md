---
article_id: af_1a86c42411606c3136610f60
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.cloitreSequence
---

# Cloitre Sequence

Limit sequence read off the approximants.

Each approximant extends the previous one and `|A_{n+2}| > n`, so position
`n` is stable from stage `n + 2` onward; out-of-range lookup defaults to `0`.
Beginning: `1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, …`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cloitre Approx](cloitre-approx.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.CloitreSequence](../../../../../../sources/v2/MathlibExt.md)
