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

open scoped ComplexConjugate
open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted (numericalRange)

-- With Mathlib's convention the scalar operator `a • id` has `numericalRange` equal to `{conj a}`.
private theorem numericalRange_smul_id (a : ℂ) :
    numericalRange (a • ContinuousLinearMap.id ℂ ℂ) = {conj a} := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    change inner ℂ (a • u) u = conj a
    rw [inner_smul_left, inner_self_eq_one_of_norm_eq_one hu, mul_one]
  · rintro rfl
    exact ⟨1, norm_one, by simp⟩

-- So the conjugate form gives `‖z - a‖ * ‖ψ‖ ≤ ‖a * ψ - z * ψ‖`, which holds with equality, also
-- for nonreal `a`.
example (a z ψ : ℂ) : ‖z - a‖ * ‖ψ‖ ≤ ‖a * ψ - z * ψ‖ := by
  simpa [numericalRange_smul_id, dist_eq_norm, ← map_sub] using
    infDist_conj_numericalRange_mul_norm_le_norm_sub_smul_apply
      (a • ContinuousLinearMap.id ℂ ℂ) ψ z

-- The conjugate is needed: without it the bound fails for `T = I • id`, `ψ = 1` and `z = I`, where
-- it would give `dist I (-I) ≤ 0`.
example : ¬ ∀ (T : ℂ →L[ℂ] ℂ) (ψ z : ℂ),
    Metric.infDist z (numericalRange T) * ‖ψ‖ ≤ ‖(T - z • ContinuousLinearMap.id ℂ ℂ) ψ‖ := by
  intro h
  have h' := h (Complex.I • ContinuousLinearMap.id ℂ ℂ) 1 Complex.I
  rw [numericalRange_smul_id, Complex.conj_I, Metric.infDist_singleton] at h'
  norm_num [Complex.ext_iff] at h'

-- The conjugate form needs no completeness: on every complex inner product space, `T - z • id` is
-- bounded below by a positive constant when `conj z` is off the closure of `numericalRange T`.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (z : ℂ)
    (hW : (numericalRange T).Nonempty) (hz : conj z ∉ closure (numericalRange T)) :
    ∃ c > 0, ∀ ψ : E, c * ‖ψ‖ ≤ ‖T ψ - z • ψ‖ :=
  ⟨_, (Metric.infDist_pos_iff_notMem_closure hW).1 hz, fun ψ => by
    simpa using infDist_conj_numericalRange_mul_norm_le_norm_sub_smul_apply T ψ z⟩

end MathlibExt.Analysis.OperatorTheory.NumericalRangeDistanceLowerBoundWanted
