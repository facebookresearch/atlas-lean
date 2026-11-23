/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.Topology
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Path

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Boundary maps for the actual classical two-cell

A based loop is traced along the bottom edge of the max-norm square. The
other three edges are sent to its basepoint. Agreement at the two bottom
corners makes this an actual continuous map on the original cell boundary.
The source boundary and target space may have independent universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u v

namespace Topology.CWComplex

/-- The boundary of the actual classical two-cell. -/
abbrev classicalCellSquareBoundary : Type u :=
  (classicalCellDiskPair.{u} 2).snd

/-- A coordinate of the original square-boundary point. -/
def classicalCellSquareCoord (i : Fin 2) (z : classicalCellSquareBoundary.{u}) : ℝ :=
  z.down.val i

/-- The max norm of a point on the original boundary is one. -/
theorem classicalCellSquare_norm (z : classicalCellSquareBoundary.{u}) :
    ‖z.down.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using z.down.property

/-- Each original coordinate lies between minus one and one. -/
theorem classicalCellSquareCoord_bounds (i : Fin 2) (z : classicalCellSquareBoundary.{u}) :
    -1 ≤ classicalCellSquareCoord i z ∧ classicalCellSquareCoord i z ≤ 1 := by
  have h := norm_le_pi_norm z.down.val i
  rw [classicalCellSquare_norm z, Real.norm_eq_abs] at h
  exact abs_le.mp h

/-- The original boundary coordinates are continuous. -/
theorem continuous_classicalCellSquareCoord (i : Fin 2) :
    Continuous (classicalCellSquareCoord.{u} i) :=
  (continuous_apply i).comp (continuous_subtype_val.comp continuous_uliftDown)

/-- The affine parameter along the bottom edge, defined on the whole boundary. -/
def classicalCellSquareParameter : C(classicalCellSquareBoundary.{u}, I) where
  toFun z := ⟨(classicalCellSquareCoord 0 z + 1) / 2, by
    obtain ⟨h₀, h₁⟩ := classicalCellSquareCoord_bounds 0 z
    constructor <;> linarith⟩
  continuous_toFun := by
    exact (((continuous_classicalCellSquareCoord 0).add continuous_const).div_const 2).subtype_mk
      (fun z => by
        change 0 ≤ (classicalCellSquareCoord 0 z + 1) / 2 ∧
          (classicalCellSquareCoord 0 z + 1) / 2 ≤ 1
        obtain ⟨h₀, h₁⟩ := classicalCellSquareCoord_bounds 0 z
        constructor <;> linarith)

/-- The bottom parameter is zero at the left endpoint. -/
theorem classicalCellSquareParameter_eq_zero (z : classicalCellSquareBoundary.{u})
    (h : classicalCellSquareCoord 0 z = -1) : classicalCellSquareParameter z = 0 := by
  apply Subtype.ext
  change (classicalCellSquareCoord 0 z + 1) / 2 = 0
  rw [h]
  norm_num

/-- The bottom parameter is one at the right endpoint. -/
theorem classicalCellSquareParameter_eq_one (z : classicalCellSquareBoundary.{u})
    (h : classicalCellSquareCoord 0 z = 1) : classicalCellSquareParameter z = 1 := by
  apply Subtype.ext
  change (classicalCellSquareCoord 0 z + 1) / 2 = 1
  rw [h]
  norm_num

/-- The bottom edge of the original boundary. -/
def classicalCellSquareBottom : Set classicalCellSquareBoundary.{u} :=
  {z | classicalCellSquareCoord 1 z = -1}

/-- The other three edges of the original boundary. -/
def classicalCellSquareOtherEdges : Set classicalCellSquareBoundary.{u} :=
  {z | classicalCellSquareCoord 0 z = -1 ∨
    classicalCellSquareCoord 0 z = 1 ∨ classicalCellSquareCoord 1 z = 1}

/-- The original bottom edge is closed in the boundary. -/
theorem isClosed_classicalCellSquareBottom : IsClosed classicalCellSquareBottom.{u} :=
  isClosed_eq (continuous_classicalCellSquareCoord 1) continuous_const

/-- The union of the original other edges is closed in the boundary. -/
theorem isClosed_classicalCellSquareOtherEdges : IsClosed classicalCellSquareOtherEdges.{u} :=
  (isClosed_eq (continuous_classicalCellSquareCoord 0) continuous_const).union
    ((isClosed_eq (continuous_classicalCellSquareCoord 0) continuous_const).union
      (isClosed_eq (continuous_classicalCellSquareCoord 1) continuous_const))

/-- Every original boundary point belongs to the bottom or another edge. -/
theorem classicalCellSquare_edge_cover (z : classicalCellSquareBoundary.{u}) :
    z ∈ classicalCellSquareBottom ∨ z ∈ classicalCellSquareOtherEdges := by
  by_contra h
  obtain ⟨hb, ho⟩ := not_or.mp h
  change classicalCellSquareCoord 1 z ≠ -1 at hb
  have hl : classicalCellSquareCoord 0 z ≠ -1 := fun hz => ho (Or.inl hz)
  have hr : classicalCellSquareCoord 0 z ≠ 1 := fun hz => ho (Or.inr (Or.inl hz))
  have ht : classicalCellSquareCoord 1 z ≠ 1 := fun hz => ho (Or.inr (Or.inr hz))
  have hnorm : ‖z.down.val‖ < 1 := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro i
    fin_cases i
    · change |classicalCellSquareCoord 0 z| < 1
      obtain ⟨h₀, h₁⟩ := classicalCellSquareCoord_bounds 0 z
      apply abs_lt.mpr
      constructor
      · by_contra hn
        simp only [not_lt] at hn
        apply hl
        linarith
      · by_contra hn
        simp only [not_lt] at hn
        apply hr
        linarith
    · change |classicalCellSquareCoord 1 z| < 1
      obtain ⟨h₀, h₁⟩ := classicalCellSquareCoord_bounds 1 z
      apply abs_lt.mpr
      constructor
      · by_contra hn
        simp only [not_lt] at hn
        apply hb
        linarith
      · by_contra hn
        simp only [not_lt] at hn
        apply ht
        linarith
  have heq := classicalCellSquare_norm z
  linarith

variable {X : Type v} [TopologicalSpace X] {x : X}

private theorem classicalCellSquare_trace_eq_basepoint (η : Path x x)
    (z : classicalCellSquareBoundary.{u})
    (hb : z ∈ classicalCellSquareBottom) (ho : z ∈ classicalCellSquareOtherEdges) :
    η (classicalCellSquareParameter z) = x := by
  change classicalCellSquareCoord 1 z = -1 at hb
  rcases ho with hl | hr | ht
  · rw [classicalCellSquareParameter_eq_zero z hl]
    exact η.source
  · rw [classicalCellSquareParameter_eq_one z hr]
    exact η.target
  · exfalso
    linarith

/-- The actual boundary map traces the chosen loop along the bottom edge
and sends the other three edges to its original basepoint. -/
def classicalCellSquareLoopMap (η : Path x x) : C(classicalCellSquareBoundary.{u}, X) := by
  classical
  exact
    { toFun := fun z =>
        if z ∈ classicalCellSquareBottom then η (classicalCellSquareParameter z) else x
      continuous_toFun := by
        apply Continuous.if
        · intro z hz
          rw [frontier_eq_closure_inter_closure] at hz
          change z ∈ closure classicalCellSquareBottom ∧
            z ∈ closure classicalCellSquareBottomᶜ at hz
          have hb : z ∈ classicalCellSquareBottom := by
            simpa only [isClosed_classicalCellSquareBottom.closure_eq] using hz.1
          have hcomp : classicalCellSquareBottomᶜ ⊆ classicalCellSquareOtherEdges := by
            intro z hz
            exact (classicalCellSquare_edge_cover z).resolve_left hz
          have ho : z ∈ classicalCellSquareOtherEdges := by
            have h := (closure_mono hcomp) hz.2
            simpa only [isClosed_classicalCellSquareOtherEdges.closure_eq] using h
          exact classicalCellSquare_trace_eq_basepoint η z hb ho
        · exact η.continuous.comp classicalCellSquareParameter.continuous
        · exact continuous_const }

/-- On the actual bottom edge, the boundary map uses the original loop parameter. -/
theorem classicalCellSquareLoopMap_bottom (η : Path x x)
    (z : classicalCellSquareBoundary.{u}) (hz : z ∈ classicalCellSquareBottom) :
    classicalCellSquareLoopMap η z = η (classicalCellSquareParameter z) := by
  classical
  change (if z ∈ classicalCellSquareBottom then _ else x) = _
  rw [ite_eq_left hz]

/-- On each of the other three original edges, the boundary map is the basepoint. -/
theorem classicalCellSquareLoopMap_other (η : Path x x)
    (z : classicalCellSquareBoundary.{u}) (hz : z ∈ classicalCellSquareOtherEdges) :
    classicalCellSquareLoopMap η z = x := by
  classical
  by_cases hb : z ∈ classicalCellSquareBottom
  · rw [classicalCellSquareLoopMap_bottom η z hb]
    exact classicalCellSquare_trace_eq_basepoint η z hb hz
  · change (if z ∈ classicalCellSquareBottom then _ else x) = x
    rw [ite_eq_right hb]

/-- A corner of the actual square, with both signed coordinates of norm one. -/
def classicalCellSquareVertex (a b : ℝ) (ha : |a| = 1) (hb : |b| = 1) :
    classicalCellSquareBoundary.{u} :=
  ULift.up ⟨![a, b], by
    have hle : ‖(![a, b] : Fin 2 → ℝ)‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      fin_cases i
      · change ‖a‖ ≤ 1
        simpa only [Real.norm_eq_abs, ha] using (le_rfl : (1 : ℝ) ≤ 1)
      · change ‖b‖ ≤ 1
        simpa only [Real.norm_eq_abs, hb] using (le_rfl : (1 : ℝ) ≤ 1)
    have hge : 1 ≤ ‖(![a, b] : Fin 2 → ℝ)‖ := by
      have h := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) (0 : Fin 2)
      change ‖a‖ ≤ ‖(![a, b] : Fin 2 → ℝ)‖ at h
      simpa only [Real.norm_eq_abs, ha] using h
    simpa only [Metric.mem_sphere, dist_zero_right] using le_antisymm hle hge⟩

/-- The bottom left corner of the original square boundary. -/
def classicalCellSquareBottomLeft : classicalCellSquareBoundary.{u} :=
  classicalCellSquareVertex (-1) (-1) (by norm_num) (by norm_num)

/-- The bottom right corner of the original square boundary. -/
def classicalCellSquareBottomRight : classicalCellSquareBoundary.{u} :=
  classicalCellSquareVertex 1 (-1) (by norm_num) (by norm_num)

/-- The top right corner of the original square boundary. -/
def classicalCellSquareTopRight : classicalCellSquareBoundary.{u} :=
  classicalCellSquareVertex 1 1 (by norm_num) (by norm_num)

/-- The top left corner of the original square boundary. -/
def classicalCellSquareTopLeft : classicalCellSquareBoundary.{u} :=
  classicalCellSquareVertex (-1) 1 (by norm_num) (by norm_num)

/-- The actual bottom left corner maps to the original loop basepoint. -/
@[simp]
theorem classicalCellSquareLoopMap_bottomLeft (η : Path x x) :
    classicalCellSquareLoopMap η classicalCellSquareBottomLeft.{u} = x :=
  classicalCellSquareLoopMap_other η _ (Or.inl rfl)

/-- The actual bottom right corner maps to the original loop basepoint. -/
@[simp]
theorem classicalCellSquareLoopMap_bottomRight (η : Path x x) :
    classicalCellSquareLoopMap η classicalCellSquareBottomRight.{u} = x :=
  classicalCellSquareLoopMap_other η _ (Or.inr (Or.inl rfl))

/-- The actual top right corner maps to the original loop basepoint. -/
@[simp]
theorem classicalCellSquareLoopMap_topRight (η : Path x x) :
    classicalCellSquareLoopMap η classicalCellSquareTopRight.{u} = x :=
  classicalCellSquareLoopMap_other η _ (Or.inr (Or.inl rfl))

/-- The actual top left corner maps to the original loop basepoint. -/
@[simp]
theorem classicalCellSquareLoopMap_topLeft (η : Path x x) :
    classicalCellSquareLoopMap η classicalCellSquareTopLeft.{u} = x :=
  classicalCellSquareLoopMap_other η _ (Or.inl rfl)

end Topology.CWComplex
