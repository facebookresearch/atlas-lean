/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MoserWormCover

/-! Direct upstream use, populated area families and geometric boundary cases. -/

open MeasureTheory Set
open MoserConvexWormCoverConstant

example : Nonempty UnitArc := inferInstance

example : eVariationOn straightPath Set.univ = 1 := straightPath_length

example : ¬ ∃ arc : UnitArc, ∃ z : ℂ, ∀ t, arc.path t = z := by
  rintro ⟨arc, z, hz⟩
  have hzero : eVariationOn arc.path Set.univ = 0 := by
    apply eVariationOn.constant_on
    rintro u ⟨x, _, rfl⟩ v ⟨y, _, rfl⟩
    rw [hz x, hz y]
  rw [arc.length_eq_one] at hzero
  exact one_ne_zero hzero

example : ¬ CoversEveryUnitArc (∅ : Set ℂ) := empty_not_covers

example : ¬ IsConvexUniversalCover (∅ : Set ℂ) := by
  intro h
  exact Set.not_nonempty_empty h.1

example : ¬ IsUniversalCover (∅ : Set ℂ) := by
  intro h
  exact Set.not_nonempty_empty h.1

example (z : ℂ) : ¬ CoversEveryUnitArc ({z} : Set ℂ) := by
  intro h
  obtain ⟨angle, translation, hm⟩ := h straightUnitArc
  let a : ArcParameter := ⟨0, by constructor <;> norm_num⟩
  let b : ArcParameter := ⟨1, by constructor <;> norm_num⟩
  have ha : move angle translation (straightUnitArc.path a) = z :=
    Set.mem_singleton_iff.mp (hm a)
  have hb : move angle translation (straightUnitArc.path b) = z :=
    Set.mem_singleton_iff.mp (hm b)
  have heq := (move_isometry angle translation).injective (ha.trans hb.symm)
  norm_num [straightUnitArc, straightPath, a, b] at heq

example : ¬ ∃ angle : ℝ, ∃ translation : ℂ,
    ∀ z : ℂ, move angle translation z = star z := by
  rintro ⟨angle, translation, h⟩
  have ht : translation = 0 := by simpa [move] using h 0
  have he : Complex.exp (angle * Complex.I) = 1 := by simpa [move, ht] using h 1
  have hi : Complex.I = -Complex.I := by simpa [move, ht, he] using h Complex.I
  have him := congrArg Complex.im hi
  norm_num at him

example : CoversEveryUnitArc (Metric.closedBall (0 : ℂ) 1) := closedBall_one_covers

example : convexCoverAreas.Nonempty := convexCoverAreas_nonempty

example : coverAreas.Nonempty := coverAreas_nonempty

example : convexCoverAreaInfimum ≠ ⊤ := convexCoverAreaInfimum_ne_top

example : coverAreaInfimum ≠ ⊤ := coverAreaInfimum_ne_top

example : nonconvexWormCoverConstant ≤ convexWormCoverConstant := nonconvex_le_convex

example : ENNReal.ofReal convexWormCoverConstant = convexCoverAreaInfimum :=
  ENNReal.ofReal_toReal convexCoverAreaInfimum_ne_top

example : ENNReal.ofReal nonconvexWormCoverConstant = coverAreaInfimum :=
  ENNReal.ofReal_toReal coverAreaInfimum_ne_top

example {Ω : Set ℂ} (h : IsConvexUniversalCover Ω) : NullMeasurableSet Ω volume :=
  h.nullMeasurableSet
