---
article_id: af_9a277a866cf67972ab2fed6f
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsApostolBernoulliSequence
---

# Apostol Bernoulli Number

Apostol-Bernoulli numbers `βₖ(α)` (concept `jis_sem_b4b0e1e624b9b6eac0d29207`,
source statement `jis_5ab17288071712819e845b9a`, equation `eq21111`): for `α ∈ ℂ`
with `α ≠ 0, 1`, the sequence `β(α)` is characterized by the exponential generating
function `t / (α * e ^ t - 1) = ∑ βₖ(α) * t ^ k / k!` for `|t| < |log α|`.
Here `Complex.log` is the principal-branch complex logarithm, so
`‖Complex.log α‖` renders the source's `|log α|`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ApostolBernoulliNumber](../../../../sources/v2/MathlibExt.md)
