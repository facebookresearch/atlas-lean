---
article_id: af_e08810b458e980c496181c13
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted.besicovitch_kakeya_compact_measure_zero
---

# Besicovitch Kakeya

There exists a measurable compact `K ⊆ EuclideanSpace ℝ (Fin 2)` with `volume K = 0` such that
every unit vector `v` has a translate `a + [0, 1]·v ⊆ K`. Source: A. S. Besicovitch, Math. Z. 27
(1928) 312–320 and S. Kakeya, Tohoku Rep. 6 (1917); Perron-tree gives compact measure-zero Kakeya
set; Lean states compact Lebesgue-null oriented version in ℝ² with segments `a+t•v`, `t∈[0, 1]`.

The proof here follows T. W. Körner, "Besicovitch via Baire", Studia Math. 158 (2003): a
Baire-category argument in the Hausdorff metric space of compact sets, not a Perron-tree
construction.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.MeasureTheory.Geometry.BesicovitchKakeya](../../../../sources/v2/MathlibExt.md)
