---
article_id: af_e076e57c139b077294f55308
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Geometry.EllipticBilliard602Wanted.conjecture
---

# Conjecture

Invariant k₆₀₂ from [AMR-050-0031] (Reznik–Garcia–Koiller 2021, Table row
k₆₀₂, arXiv:2004.12497): for every `N`, with outer ellipse
`dist X f₁ + dist X f₂ = a`, center `O = (1 / 2 : ℝ) • (f₁ + f₂)`,
`dist f₁ f₂ < a`, and confocal caustic `dist f₁ f₂ < ac < a`, there is one
shared `C` such that every `N`-periodic Poncelet orbit `P` (on-ellipse,
`N`-periodic, distinct consecutive vertices, each sideline uniquely meeting
the caustic) with pedal feet `Q₁ Q₂` (on-sideline closest points to
`f₁ f₂`) satisfies
`(∏ i : Fin N, dist f₁ (Q₁ i)) * (∏ i : Fin N, dist f₂ (Q₂ i)) = C`.
`P'`, `P''`, areas, and antipedal data are source context only and do not
enter the binders. As the source presents the item as open, this states the
question as a proposition.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Geometry.EllipticBilliard602Wanted](../../../../../sources/v2/WantedExt.md)
