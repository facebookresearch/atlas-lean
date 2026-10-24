---
article_id: af_7f6c8727ae709236bcfbec94
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.RademacherEnfloTypeWanted.RademacherEnfloType.IsRademacherType
---

# Is Rademacher Type

`IsRademacherType X C p` is the proposition that for all `n ≥ 1`, and `x₁, …, xₙ ∈ X`

`𝔼‖∑ j ∈ {1,…,n}, εⱼxⱼ‖ᵖ ≤ Cᵖ ∑ j ∈ {1,…,n}, ‖xⱼ‖ᵖ`

where `ε₁, …, εₙ` is a sequence of independent Rademacher variables.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Rademacher Product Distribution](rademacher-product-distribution.md)

## Sources

- [WantedExt, WantedExt.Analysis.RademacherEnfloTypeWanted](../../../../../sources/v2/WantedExt.md)
