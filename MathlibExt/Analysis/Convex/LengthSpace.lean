/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import MathlibExt.Topology.MetricSpace.LengthSpace

/-!
# Convex sets and normed spaces are length spaces

In a real normed space, the straight-line path `Path.segment x y` has length at
most `edist x y`. Hence convex sets with the inherited metric, and normed spaces
themselves, are length spaces.

## Main results

* `Path.eVariationOn_segment_le`: the segment has length at most `edist`.
* `Convex.isLengthSpace`: convex sets with the inherited metric are length spaces.
* `isLengthSpace_of_normedSpace`: a real normed space is a length space.

## References

* AKP, *Alexandrov geometry: foundations*, AMS GSM 236, 2024
  (arXiv:1903.08539v6), Section "Length spaces", `metr.tex` l.507.
-/

@[expose] public section

/-- The straight-line path from `x` to `y` has length at most `edist x y`. -/
theorem Path.eVariationOn_segment_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) :
    eVariationOn (Path.segment x y) Set.univ ≤ edist x y := by
  have hKcoe : ((⟨dist x y, dist_nonneg⟩ : NNReal) : ℝ) = dist x y :=
    NNReal.coe_mk _ _
  have hlipW : LipschitzWith (⟨dist x y, dist_nonneg⟩ : NNReal)
      ⇑(AffineMap.lineMap (k := ℝ) x y) :=
    LipschitzWith.of_dist_le_mul (fun s t : ℝ => by
      have hEq : dist ((AffineMap.lineMap (k := ℝ) x y) s)
          ((AffineMap.lineMap (k := ℝ) x y) t) =
          ((⟨dist x y, dist_nonneg⟩ : NNReal) : ℝ) * dist s t := by
        rw [dist_lineMap_lineMap, hKcoe]
        exact mul_comm _ _
      exact le_of_eq hEq)
  have hlip : LipschitzOnWith (⟨dist x y, dist_nonneg⟩ : NNReal)
      ⇑(AffineMap.lineMap (k := ℝ) x y) Set.univ :=
    hlipW.lipschitzOnWith
  have hle : eVariationOn
      (⇑(AffineMap.lineMap (k := ℝ) x y) ∘ (Subtype.val : ↑unitInterval → ℝ))
      Set.univ ≤
      (NNReal.mk (dist x y) dist_nonneg : ENNReal) *
        eVariationOn (Subtype.val : ↑unitInterval → ℝ) Set.univ :=
    LipschitzOnWith.comp_eVariationOn_le hlip
      (Set.mapsTo_univ (Subtype.val : ↑unitInterval → ℝ) Set.univ)
  have hmono : MonotoneOn (Subtype.val : ↑unitInterval → ℝ) Set.univ :=
    (Subtype.mono_coe _).monotoneOn Set.univ
  have hcomp : eVariationOn (Subtype.val : ↑unitInterval → ℝ) Set.univ =
      eVariationOn (id : ℝ → ℝ) ((Subtype.val : ↑unitInterval → ℝ) '' Set.univ) :=
    eVariationOn.comp_eq_of_monotoneOn (id : ℝ → ℝ)
      (Subtype.val : ↑unitInterval → ℝ) hmono
  have hU : unitInterval = Set.Icc (0 : ℝ) 1 := rfl
  have himg : (Subtype.val : ↑unitInterval → ℝ) '' Set.univ = Set.Icc (0 : ℝ) 1 := by
    rw [Set.image_univ, Subtype.range_coe, hU]
  have hid : eVariationOn (id : ℝ → ℝ) (Set.Icc (0 : ℝ) 1) = 1 := by
    rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one]
  have hval : eVariationOn (Subtype.val : ↑unitInterval → ℝ) Set.univ = 1 := by
    rw [hcomp, himg]
    exact hid
  have hfun : ⇑(Path.segment x y) = ⇑(AffineMap.lineMap (k := ℝ) x y) ∘
      (Subtype.val : ↑unitInterval → ℝ) := by
    funext t
    exact Path.segment_apply x y t
  have hfinal : (NNReal.mk (dist x y) dist_nonneg : ENNReal) = edist x y := by
    rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, edist_dist]
  calc eVariationOn (Path.segment x y) Set.univ
      = eVariationOn (⇑(AffineMap.lineMap (k := ℝ) x y) ∘
          (Subtype.val : ↑unitInterval → ℝ)) Set.univ := by
        rw [hfun]
    _ ≤ (NNReal.mk (dist x y) dist_nonneg : ENNReal) *
        eVariationOn (Subtype.val : ↑unitInterval → ℝ) Set.univ := hle
    _ = edist x y := by
        rw [hval, mul_one, hfinal]

/-- A convex set in a real normed space, with the inherited metric, is a length
space: the inherited metric coincides with its length metric. -/
theorem Convex.isLengthSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : Convex ℝ s) :
    Metric.IsLengthSpace s := by
  refine Metric.isLengthSpace_iff_le.mpr fun x y => ?_
  have hmem : ∀ t : ↑unitInterval, Path.segment (x : E) (y : E) t ∈ s := by
    intro t
    rw [Path.segment_apply]
    exact Convex.lineMap_mem hs x.2 y.2 t.2
  have hcont : Continuous (fun t : ↑unitInterval =>
      (⟨Path.segment (x : E) (y : E) t, hmem t⟩ : s)) :=
    (Path.segment (x : E) (y : E)).continuous.subtype_mk hmem
  let γ : Path x y := ⟨⟨_, hcont⟩,
    Subtype.ext (Path.source (Path.segment (x : E) (y : E))),
    Subtype.ext (Path.target (Path.segment (x : E) (y : E)))⟩
  have heq : eVariationOn (⇑γ) Set.univ =
      eVariationOn (⇑(Path.segment (x : E) (y : E))) Set.univ := by
    unfold eVariationOn
    congr 1
  calc Metric.inducedLengthEdist x y
      ≤ eVariationOn (⇑γ) Set.univ :=
        Metric.inducedLengthEdist_le_eVariationOn γ
    _ = eVariationOn (⇑(Path.segment (x : E) (y : E))) Set.univ := heq
    _ ≤ edist (x : E) (y : E) := Path.eVariationOn_segment_le _ _
    _ = edist x y := (Subtype.edist_eq x y).symm

/-- A real normed space is a length space. -/
theorem isLengthSpace_of_normedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Metric.IsLengthSpace E :=
  Metric.isLengthSpace_iff_le.mpr fun x y =>
    (Metric.inducedLengthEdist_le_eVariationOn (Path.segment x y)).trans
      (Path.eVariationOn_segment_le x y)

end
