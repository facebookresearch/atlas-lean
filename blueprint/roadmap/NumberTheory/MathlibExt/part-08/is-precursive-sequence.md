---
article_id: af_80ef5f7f26f274c70c0561ea
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsPRecursiveSequence
---

# PRecursive Sequence

An integer sequence is P-recursive of order `r` with coefficient polynomials
`P₀, …, Pᵣ` if, for every `n ≥ r`,
`P₀(n) uₙ = ∑_{i=1}^r Pᵢ(n) uₙ₋ᵢ`.

The finite coefficient family prevents accidental access beyond `Pᵣ`, and the explicit
index guard records the source domain without relying on truncated subtraction.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PRecursiveSequence](../../../../sources/v2/MathlibExt.md)
