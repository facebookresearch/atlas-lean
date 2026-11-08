/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Unit planar arcs and Moser universal covers

Continuous unit-length planar arcs, direct rigid motions, actual-area families and
finite area infima for convex and unrestricted universal covers.

Source: Optimization Problems, constant 13a; Panraksa and Wichiramala,
Wetzel's sector covers unit arcs (2021); Fässler and Orponen,
Curve packing and modulus estimates (2018).

The geometric definitions and proved support laws retain the original
`MoserConvexWormCoverConstant` namespace. Literature bounds and missing proofs
are specified in the separate opt-in wishlist library.
-/

@[expose] public section

open MeasureTheory Set

namespace MoserConvexWormCoverConstant

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
abbrev ArcParameter := Set.Icc (0 : ℝ) 1

/-- A continuous parametrized planar curve of metric length exactly one. Source: Optimization
Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
structure UnitArc where
  path : C(ArcParameter, ℂ)
  length_eq_one : eVariationOn path Set.univ = 1

/-- Rotation followed by translation, with neither reflection nor rescaling. Source:
Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
noncomputable def move (angle : ℝ) (translation z : ℂ) : ℂ :=
  Complex.exp (angle * Complex.I) * z + translation

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem move_isometry (angle : ℝ) (translation : ℂ) : Isometry (move angle translation) := by
  apply Isometry.of_dist_eq
  intro z w
  simp [move, dist_eq_norm, ← mul_sub]

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def straightPath : C(ArcParameter, ℂ) :=
  ⟨fun t => (t.1 : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem parameter_variation :
    eVariationOn (Subtype.val : ArcParameter → ℝ) Set.univ = 1 := by
  have himage : (Subtype.val : ArcParameter → ℝ) '' Set.univ = Set.Icc 0 1 := by
    ext x
    constructor
    · rintro ⟨t, _, rfl⟩
      exact t.2
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have h := eVariationOn.comp_eq_of_monotoneOn (id : ℝ → ℝ) (t := Set.univ)
    (Subtype.val : ArcParameter → ℝ) (fun _ _ _ _ h => h)
  simpa [Function.comp_def, himage, eVariationOn_id_Icc] using h

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem straightPath_length : eVariationOn straightPath Set.univ = 1 := by
  apply le_antisymm
  · have h := Complex.isometry_ofReal.lipschitzWith.lipschitzOnWith.comp_eVariationOn_le
      (g := (Subtype.val : ArcParameter → ℝ)) (s := Set.univ) (t := Set.univ)
      (fun _ _ => Set.mem_univ _)
    simpa [Function.comp_def, straightPath, parameter_variation] using h
  · let a : ArcParameter := ⟨0, by constructor <;> norm_num⟩
    let b : ArcParameter := ⟨1, by constructor <;> norm_num⟩
    have h := eVariationOn.edist_le straightPath (s := Set.univ) (x := a) (y := b)
      (Set.mem_univ _) (Set.mem_univ _)
    simpa [a, b, straightPath, edist_dist, Complex.dist_eq] using h

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def straightUnitArc : UnitArc := ⟨straightPath, straightPath_length⟩

/-- The straight unit arc witnesses nonemptiness of the curve domain.
Source: Optimization Problems, constant 13a (frozen 2c1968cd); interval-arc adaptation.
-/
instance : Nonempty UnitArc := ⟨straightUnitArc⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def CoversEveryUnitArc (Ω : Set ℂ) : Prop :=
  ∀ arc : UnitArc, ∃ angle : ℝ, ∃ translation : ℂ,
    ∀ t : ArcParameter, move angle translation (arc.path t) ∈ Ω

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem CoversEveryUnitArc.nonempty {Ω : Set ℂ} (h : CoversEveryUnitArc Ω) : Ω.Nonempty := by
  obtain ⟨angle, translation, h⟩ := h straightUnitArc
  let t : ArcParameter := ⟨0, by constructor <;> norm_num⟩
  exact ⟨_, h t⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem empty_not_covers : ¬ CoversEveryUnitArc (∅ : Set ℂ) := by
  intro h
  exact Set.not_nonempty_empty h.nonempty

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def IsConvexUniversalCover (Ω : Set ℂ) : Prop :=
  Ω.Nonempty ∧ Convex ℝ Ω ∧ CoversEveryUnitArc Ω

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def IsUniversalCover (Ω : Set ℂ) : Prop :=
  Ω.Nonempty ∧ CoversEveryUnitArc Ω

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem IsConvexUniversalCover.nullMeasurableSet {Ω : Set ℂ}
    (h : IsConvexUniversalCover Ω) : NullMeasurableSet Ω volume :=
  h.2.1.nullMeasurableSet volume

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem IsConvexUniversalCover.isUniversalCover {Ω : Set ℂ}
    (h : IsConvexUniversalCover Ω) : IsUniversalCover Ω :=
  ⟨h.1, h.2.2⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def convexCoverAreas : Set ENNReal :=
  {a | ∃ Ω : Set ℂ, IsConvexUniversalCover Ω ∧ volume Ω = a}

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def coverAreas : Set ENNReal :=
  {a | ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω = a}

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def convexCoverAreaInfimum : ENNReal := sInf convexCoverAreas

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def coverAreaInfimum : ENNReal := sInf coverAreas

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem closedBall_one_covers : CoversEveryUnitArc (Metric.closedBall (0 : ℂ) 1) := by
  intro arc
  let start : ArcParameter := ⟨0, by constructor <;> norm_num⟩
  refine ⟨0, -arc.path start, ?_⟩
  intro t
  have h := eVariationOn.edist_le arc.path (s := Set.univ) (x := t) (y := start)
    (Set.mem_univ _) (Set.mem_univ _)
  rw [arc.length_eq_one] at h
  have hd := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) h
  have hd' : dist (arc.path t) (arc.path start) ≤ 1 := by
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_one] using hd
  simpa [Metric.mem_closedBall, move, Complex.dist_eq, sub_eq_add_neg] using hd'

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem closedBall_one_isConvexUniversalCover :
    IsConvexUniversalCover (Metric.closedBall (0 : ℂ) 1) := by
  refine ⟨⟨0, by simp⟩, convex_closedBall _ _, closedBall_one_covers⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem convexCoverAreas_nonempty : convexCoverAreas.Nonempty :=
  ⟨volume (Metric.closedBall (0 : ℂ) 1), _, closedBall_one_isConvexUniversalCover, rfl⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem coverAreas_nonempty : coverAreas.Nonempty :=
  ⟨volume (Metric.closedBall (0 : ℂ) 1), _,
    closedBall_one_isConvexUniversalCover.isUniversalCover, rfl⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem convexCoverAreaInfimum_ne_top : convexCoverAreaInfimum ≠ ⊤ := by
  have h : convexCoverAreaInfimum ≤ volume (Metric.closedBall (0 : ℂ) 1) :=
    sInf_le ⟨_, closedBall_one_isConvexUniversalCover, rfl⟩
  exact ne_top_of_le_ne_top (by simp [Complex.volume_closedBall]) h

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem coverAreaInfimum_ne_top : coverAreaInfimum ≠ ⊤ := by
  have h : coverAreaInfimum ≤ volume (Metric.closedBall (0 : ℂ) 1) :=
    sInf_le ⟨_, closedBall_one_isConvexUniversalCover.isUniversalCover, rfl⟩
  exact ne_top_of_le_ne_top (by simp [Complex.volume_closedBall]) h

/-- The real infimal area; finiteness is proved before this projection is used. Source:
Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
noncomputable def convexWormCoverConstant : ℝ := convexCoverAreaInfimum.toReal

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def nonconvexWormCoverConstant : ℝ := coverAreaInfimum.toReal

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem convexWormCoverConstant_nonneg : 0 ≤ convexWormCoverConstant :=
  ENNReal.toReal_nonneg

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexWormCoverConstant_nonneg : 0 ≤ nonconvexWormCoverConstant :=
  ENNReal.toReal_nonneg

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvex_le_convex : nonconvexWormCoverConstant ≤ convexWormCoverConstant := by
  apply (ENNReal.toReal_le_toReal coverAreaInfimum_ne_top convexCoverAreaInfimum_ne_top).2
  apply le_sInf
  rintro a ⟨Ω, hΩ, rfl⟩
  exact sInf_le ⟨Ω, hΩ.isUniversalCover, rfl⟩

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def halfDisk : Set ℂ :=
  {z | ‖z‖ ≤ (1 : ℝ) / 2}

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
noncomputable def halfSemidisk : Set ℂ :=
  {z | ‖z‖ ≤ (1 : ℝ) / 2 ∧ 0 ≤ z.im}

/-- A centered orientation of the closed radius-one, thirty-degree sector. Source: Optimization
Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
noncomputable def wetzelSector : Set ℂ :=
  {z | ‖z‖ ≤ 1 ∧ 0 ≤ z.re ∧ |z.im| ≤ Real.tan (Real.pi / 12) * z.re}

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexUpperBound_of_cover {r : ℝ} (hr : 0 ≤ r)
    (h : ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal r) :
    nonconvexWormCoverConstant ≤ r := by
  rcases h with ⟨Ω, hΩ, harea⟩
  have hi : coverAreaInfimum ≤ ENNReal.ofReal r :=
    (sInf_le (s := coverAreas) ⟨Ω, hΩ, rfl⟩).trans harea
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal r ≠ ⊤) hi
  simpa [nonconvexWormCoverConstant, ENNReal.toReal_ofReal hr] using hreal

end MoserConvexWormCoverConstant
