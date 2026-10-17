---
article_id: af_a98dd3388ed05d080b8438e1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted.banach_tarski_closedBall_unit
---

# Banach tarski closed Ball unit

The closed unit ball at `0` in `EuclideanSpace ℝ (Fin 3)` is finitely equidecomposable by ambient
bijective isometries with the disjoint union of two closed unit balls `closedBall c₁ 1 ∪
closedBall c₂ 1` for some centres `c₁ c₂` with `Disjoint`. Source: S. Banach and A. Tarski, Fund.
Math. 6 (1924) 244–277 original paradox; S. Wagon, The Banach–Tarski Paradox, Cambridge Univ.
Press (1993); Lean states closed unit ball duplication specialization in ℝ³ with ambient `≃ᵢ`
equidecomposability.

## Depends on

- [Finitely Equidecomposable By Isometries](finitely-equidecomposable-by-isometries.md)

## Sources

- [MathlibExt, MathlibExt.MeasureTheory.Geometry.BanachTarski](../../../../../sources/v2/MathlibExt.md)
