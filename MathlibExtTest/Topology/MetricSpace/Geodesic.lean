/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MetricSpace.Geodesic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for local geodesics in metric spaces

Lines are geodesics of the right speed, constant curves are geodesics but not closed geodesics, a
curve that does not have constant speed is not a geodesic, and the unit-speed loop around the
circle `AddCircle 1` is a closed geodesic.
-/

open Metric Set
open scoped NNReal

noncomputable section

namespace MetricGeodesicTests

/-- A line in `ℝ²` is a unit-speed geodesic when its direction is a unit vector. -/
example (p v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ = 1) :
    IsGeodesicOnWithSpeed (fun t : ℝ ↦ p + t • v) univ 1 := by
  have : ‖v‖₊ = 1 := by ext; simpa using hv
  simpa [this] using isGeodesicOnWithSpeed_lineMap p v univ

/-- Constant curves are geodesics of speed `0`, but not closed geodesics. -/
example (p : ℝ) : IsGeodesic (fun _ : ℝ ↦ p) ∧ ¬ IsClosedGeodesic (fun _ : ℝ ↦ p) :=
  ⟨isGeodesic_const p, not_isClosedGeodesic_const p⟩

/-- `t ↦ t ^ 2` does not have constant speed, so it is not a geodesic of `ℝ`. -/
example : ¬ IsGeodesic (fun t : ℝ ↦ t ^ 2) := by
  rintro ⟨c, hc⟩
  obtain ⟨ε, hε, h⟩ := hc 0 (mem_univ 0)
  have key (δ : ℝ) (hδ : 0 < δ) (hδε : δ < ε) : δ = c := by
    have h1 := h 0 (mem_univ _) δ (mem_univ _) (by simpa using hε) (by simpa [abs_of_pos hδ])
    simp only [edist_dist, Real.dist_eq, zero_sub, abs_neg, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, abs_of_pos hδ, abs_of_pos (pow_pos hδ 2)] at h1
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg c)] at h1
    have := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp h1
    nlinarith
  have h1 := key (ε / 2) (by positivity) (by linarith)
  have h2 := key (ε / 4) (by positivity) (by linarith)
  linarith

/-- On the circle `AddCircle 1`, nearby points are at distance `|s - t|`. -/
theorem dist_addCircle_coe {s t : ℝ} (h : |s - t| ≤ 1 / 2) :
    dist (s : AddCircle (1 : ℝ)) t = |s - t| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub,
    AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero]
  simpa using h

/-- The unit-speed loop `t ↦ (t : AddCircle 1)` is a closed geodesic: it realizes distances on
intervals of length `1/2`, has period `1`, and is not constant. -/
theorem isClosedGeodesic_addCircle : IsClosedGeodesic (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) := by
  refine ⟨⟨1, fun t _ ↦ ⟨1 / 4, by norm_num, fun t₁ _ t₂ _ h₁ h₂ ↦ ?_⟩⟩,
    ⟨1, one_pos, fun t ↦ by simp⟩, 0, 1 / 2, ?_⟩
  · have h : |t₁ - t₂| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [abs_lt.mp h₁, abs_lt.mp h₂]
    rw [edist_dist, edist_dist, dist_addCircle_coe h, Real.dist_eq, ENNReal.coe_one, one_mul]
  · intro h
    have h1 : ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = |1 / 2| :=
      (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr (by norm_num)
    have h2 : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simpa using h.symm
    rw [h2, norm_zero] at h1
    norm_num at h1

end MetricGeodesicTests
