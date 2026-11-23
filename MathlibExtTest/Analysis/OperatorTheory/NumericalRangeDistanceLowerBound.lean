/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBound
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted

-- Scalar multiplication has the singleton numerical range {a}, including for nonreal a.
example (a z ψ : ℂ) : ‖a * ψ - z * ψ‖ ≥ ‖z - a‖ * ‖ψ‖ := by
  let T := a • ContinuousLinearMap.id ℂ ℂ
  have hN : {a} = {w : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ inner ℂ u (T u) = w} := by
    ext w
    constructor
    · rintro rfl
      exact ⟨1, norm_one, by simp [T]⟩
    · rintro ⟨u, hu, rfl⟩
      change inner ℂ u (a • u) = a
      rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one hu, mul_one]
  simpa [T, dist_eq_norm] using
    infDist_numericalRange_mul_norm_le_norm_sub_smul_apply ℂ T {a} hN ψ z

-- The zero-dimensional space has no unit vectors, so its numerical range is empty.
example (T : EuclideanSpace ℂ (Fin 0) →L[ℂ] EuclideanSpace ℂ (Fin 0))
    (z : ℂ) (ψ : EuclideanSpace ℂ (Fin 0)) :
    ‖T ψ - z • ψ‖ ≥ Metric.infDist z ∅ * ‖ψ‖ := by
  apply infDist_numericalRange_mul_norm_le_norm_sub_smul_apply _ T ∅ _ ψ z
  symm
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro w ⟨u, hu, -⟩
  simp [Subsingleton.elim u 0] at hu

end MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted
