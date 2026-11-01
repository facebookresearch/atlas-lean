---
article_id: af_1ae9aa2e4785bcd2da0d0894
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.RademacherEnfloTypeWanted.RademacherEnfloType.IsEnfloType
---

# Is Enflo Type

`IsEnfloType X C p` is the proposition that for all `n ≥ 1`, and `f : {-1,1}ⁿ → X`

`𝔼‖ (f(ε) - f(-ε)) / 2 ‖ᵖ ≤ Cᵖ ∑ j ∈ {1,…,n}, 𝔼‖Dⱼf(ε)‖ᵖ`

where `ε₁, …, εₙ` is a sequence of independent Rademacher variables.

## Depends on

This node has no prerequisites.

## Proof depends on

- [D](d.md)
- [Rademacher Product Distribution](rademacher-product-distribution.md)

## Sources

- [WantedExt, WantedExt.Analysis.RademacherEnfloTypeWanted](../../../../../sources/v2/WantedExt.md)
