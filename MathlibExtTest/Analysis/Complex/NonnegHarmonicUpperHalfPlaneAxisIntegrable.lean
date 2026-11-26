/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.NonnegHarmonicUpperHalfPlaneAxisIntegrable

/-! # Tests for vanishing of axis-integrable nonnegative harmonic functions -/

namespace MathlibExtTest.Analysis.Complex.NonnegHarmonicUpperHalfPlaneAxisIntegrable

open Filter InnerProductSpace MeasureTheory Set
open MathlibExt.Analysis.Complex.NonnegHarmonicUpperHalfPlaneAxisIntegrableWanted
open scoped Topology

-- Exercise the public theorem with the source hypotheses and named arguments.
example (f : ℂ → ℝ)
    (hharm : HarmonicOnNhd f UpperHalfPlane.upperHalfPlaneSet)
    (hnonneg : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ f z)
    (hint : IntegrableOn (fun y : ℝ => |f (Complex.I * (y : ℂ))|) (Ioi (0 : ℝ))) :
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z = 0 :=
  eq_zero_of_harmonicOnNhd_upperHalfPlane_of_nonneg_of_integrableOn_imagAxis
    (f := f) (hharm := hharm) (hnonneg := hnonneg) (hint := hint)

private noncomputable def lowerHalfPlaneValue (z : ℂ) : ℝ :=
  max 0 (-z.im)

private theorem lowerHalfPlaneValue_eq_zero {z : ℂ} (hz : 0 < z.im) :
    lowerHalfPlaneValue z = 0 :=
  max_eq_left (neg_nonpos.mpr hz.le)

-- A concrete admissible function may be nonzero outside the upper half-plane.
-- Evaluate the theorem at a point that is not on the imaginary axis.
example :
    lowerHalfPlaneValue (1 + Complex.I) = 0 ∧ lowerHalfPlaneValue (-Complex.I) = 1 := by
  have hharm : HarmonicOnNhd lowerHalfPlaneValue UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    have heq : lowerHalfPlaneValue =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
      exact lowerHalfPlaneValue_eq_zero hw
    exact (harmonicAt_congr_nhds heq).2 (by simp)
  have hnonneg : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ lowerHalfPlaneValue z :=
    fun _ _ => le_max_left _ _
  have hint : IntegrableOn (fun y : ℝ => |lowerHalfPlaneValue (Complex.I * (y : ℂ))|)
      (Ioi (0 : ℝ)) := by
    refine integrableOn_zero.congr_fun (fun y (hy : 0 < y) => ?_) measurableSet_Ioi
    rw [lowerHalfPlaneValue_eq_zero (by simpa [Complex.mul_im] using hy), abs_zero]
  refine ⟨eq_zero_of_harmonicOnNhd_upperHalfPlane_of_nonneg_of_integrableOn_imagAxis
    lowerHalfPlaneValue hharm hnonneg hint _ ?_, ?_⟩
  · change 0 < (1 + Complex.I).im
    simp
  · simp [lowerHalfPlaneValue]

end MathlibExtTest.Analysis.Complex.NonnegHarmonicUpperHalfPlaneAxisIntegrable
