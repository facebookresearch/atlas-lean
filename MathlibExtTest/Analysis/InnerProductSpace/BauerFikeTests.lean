/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.BauerFike
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Tests for Bauer–Fike eigenvalue perturbation for normal operators

Scalar operators are used throughout: for `A = (2 : ℂ) • 1` and
`E = (1 / 2 : ℂ) • 1`, the perturbation moves the spectrum from `{2}` to
`{5 / 2}`, a distance of exactly `‖E‖ = 1 / 2`, so every bound in
`MathlibExt.Analysis.InnerProductSpace.BauerFike` is sharp on these tests.
The resolvent bound is also checked on `EuclideanSpace ℂ (Fin 2)`, a
space of dimension greater than one.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.BauerFikeTests

open Metric
open MathlibExt.Analysis.InnerProductSpace.BauerFike

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

omit [CompleteSpace H] in
/-- Membership in the spectrum of a scalar operator. -/
private theorem mem_spectrum_smul_one_iff {μ c : ℂ} :
    μ ∈ spectrum ℂ (c • (1 : H →L[ℂ] H)) ↔ μ = c := by
  constructor
  · intro h
    by_contra hne
    have hunit : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - c • (1 : H →L[ℂ] H)) := by
      rw [Algebra.algebraMap_eq_smul_one, ← sub_smul]
      refine ⟨⟨(μ - c) • (1 : H →L[ℂ] H), (μ - c)⁻¹ • (1 : H →L[ℂ] H), ?_, ?_⟩, rfl⟩
      · rw [smul_mul_smul, mul_one, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_smul]
      · rw [smul_mul_smul, mul_one, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    exact (spectrum.mem_iff.mp h) hunit
  · intro h
    rw [h, spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, sub_self]
    exact not_isUnit_zero

omit [CompleteSpace H] in
/-- The spectrum of a scalar operator is a singleton. -/
private theorem spectrum_smul_one_eq {c : ℂ} :
    spectrum ℂ (c • (1 : H →L[ℂ] H)) = {c} := by
  ext μ
  simp only [Set.mem_singleton_iff, mem_spectrum_smul_one_iff]

omit [CompleteSpace H] [Nontrivial H] in
/-- The ring inverse of a nonzero scalar operator is the scalar operator
of the inverse scalar. -/
private theorem ringInverse_smul_one {c : ℂ} (hc : c ≠ 0) :
    Ring.inverse (c • (1 : H →L[ℂ] H)) = c⁻¹ • (1 : H →L[ℂ] H) := by
  have hunit : IsUnit (c • (1 : H →L[ℂ] H)) := by
    refine ⟨⟨c • (1 : H →L[ℂ] H), c⁻¹ • (1 : H →L[ℂ] H), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul, mul_one, mul_inv_cancel₀ hc, one_smul]
    · rw [smul_mul_smul, mul_one, inv_mul_cancel₀ hc, one_smul]
  have h1 : (c • (1 : H →L[ℂ] H)) * (c⁻¹ • (1 : H →L[ℂ] H)) = 1 := by
    rw [smul_mul_smul, mul_one, mul_inv_cancel₀ hc, one_smul]
  calc Ring.inverse (c • (1 : H →L[ℂ] H))
      = Ring.inverse (c • (1 : H →L[ℂ] H))
          * ((c • (1 : H →L[ℂ] H)) * (c⁻¹ • (1 : H →L[ℂ] H))) := by
        rw [h1, mul_one]
    _ = (Ring.inverse (c • (1 : H →L[ℂ] H)) * (c • (1 : H →L[ℂ] H)))
          * (c⁻¹ • (1 : H →L[ℂ] H)) := by rw [mul_assoc]
    _ = c⁻¹ • (1 : H →L[ℂ] H) := by rw [Ring.inverse_mul_cancel _ hunit, one_mul]

/-- The resolvent bound is an equality for the scalar operator `2 • 1`
at `z = 5`: both sides are `1 / 3`. -/
example : ‖Ring.inverse (algebraMap ℂ (ℂ →L[ℂ] ℂ) 5
      - (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖
    = (Metric.infDist 5 (spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))))⁻¹ := by
  have hspec : spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = {(2 : ℂ)} :=
    spectrum_smul_one_eq
  have hres : Ring.inverse (algebraMap ℂ (ℂ →L[ℂ] ℂ) 5
      - (2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = (3 : ℂ)⁻¹ • (1 : ℂ →L[ℂ] ℂ) := by
    rw [Algebra.algebraMap_eq_smul_one, ← sub_smul]
    have h53 : (5 : ℂ) - 2 = 3 := by norm_num
    rw [h53]
    exact ringInverse_smul_one (by norm_num)
  rw [hres, hspec, Metric.infDist_singleton, dist_eq_norm, norm_smul, norm_one,
    mul_one]
  norm_num

/-- Bauer–Fike is sharp for the scalar perturbation `2 • 1 + (1 / 2) • 1`:
the spectrum moves by exactly `‖E‖ = 1 / 2`. -/
example : Metric.infDist (5 / 2 : ℂ)
    (spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ))) = 1 / 2 := by
  have hspec : spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = {(2 : ℂ)} :=
    spectrum_smul_one_eq
  rw [hspec, Metric.infDist_singleton, dist_eq_norm]
  norm_num

/-- The Bauer–Fike bound itself, on the scalar example. -/
example : Metric.infDist (5 / 2 : ℂ)
    (spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)))
    ≤ ‖(1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ := by
  have hmem : (5 / 2 : ℂ) ∈ spectrum ℂ
      (((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) + (1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
    have hsum : ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) + (1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)
        = (5 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      module
    rw [hsum]
    exact (mem_spectrum_smul_one_iff).mpr rfl
  exact infDist_le_norm_of_mem_spectrum_add hmem

/-- The attained form: `2` is within `‖E‖ = 1 / 2` of `5 / 2`. -/
example : ∃ v ∈ spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)),
    ‖(5 / 2 : ℂ) - v‖ ≤ ‖(1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ := by
  have hmem : (5 / 2 : ℂ) ∈ spectrum ℂ
      (((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) + (1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
    have hsum : ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) + (1 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)
        = (5 / 2 : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      module
    rw [hsum]
    exact (mem_spectrum_smul_one_iff).mpr rfl
  obtain ⟨v, hv, hbound⟩ := exists_mem_spectrum_norm_sub_le hmem
  have hspec : spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = {(2 : ℂ)} :=
    spectrum_smul_one_eq
  rw [hspec] at hv
  have hv2 : v = 2 := by simpa using hv
  rw [hv2] at hbound
  exact ⟨2, by rw [hspec]; simp, hbound⟩

/-- A real scalar operator is self-adjoint. -/
private theorem isSelfAdjoint_ofReal_smul_one (r : ℝ) :
    IsSelfAdjoint (((r : ℂ)) • (1 : ℂ →L[ℂ] ℂ)) := by
  show star ((((r : ℂ)) • (1 : ℂ →L[ℂ] ℂ))) = _
  simp [star_smul]

/-- The Hausdorff form, on the real scalar perturbation
`2 • 1 + (1 / 2) • 1`: it applies with `‖E‖ = 1 / 2`. -/
example : Metric.hausdorffDist
    (spectrum ℂ ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)))
    (spectrum ℂ ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)
      + (((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)))
    ≤ ‖(((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)‖ := by
  have hA : IsSelfAdjoint ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)) :=
    isSelfAdjoint_ofReal_smul_one 2
  have hsum : ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ))
      + (((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)
      = (((5 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ) := by
    module
  have hAE : IsSelfAdjoint ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)
      + (((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)) := by
    rw [hsum]
    exact isSelfAdjoint_ofReal_smul_one (5 / 2)
  exact hausdorffDist_spectrum_le_of_isSelfAdjoint hA hAE

/-- The Hausdorff distance of `{2}` and `{5 / 2}` is exactly `1 / 2`,
so the Hausdorff form above is sharp on this example. -/
example : Metric.hausdorffDist
    (spectrum ℂ ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)))
    (spectrum ℂ ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)
      + (((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ))) = 1 / 2 := by
  have hsum : ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ))
      + (((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)
      = (((5 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ) := by
    module
  have hspecA : spectrum ℂ ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ))
      = {(((2 : ℝ) : ℂ))} := spectrum_smul_one_eq
  have hspecAE : spectrum ℂ ((((2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ)
      + (((1 / 2 : ℝ) : ℂ)) • (1 : ℂ →L[ℂ] ℂ))
      = {(((5 / 2 : ℝ) : ℂ))} := by
    rw [hsum]
    exact spectrum_smul_one_eq
  rw [hspecA, hspecAE, Metric.hausdorffDist_singleton, dist_eq_norm,
    ← Complex.ofReal_sub]
  rw [show ((2 : ℝ) - 5 / 2 : ℝ) = -(1 / 2) by norm_num, Complex.ofReal_neg, norm_neg,
    Complex.norm_real]
  norm_num

/-- The resolvent bound on `EuclideanSpace ℂ (Fin 2)`, where the
spectrum of `0` is `{0}`: at `z = 3` both sides are `1 / 3`. -/
example : ‖Ring.inverse (algebraMap ℂ
      (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) 3
      - (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))‖
    = (Metric.infDist 3 (spectrum ℂ
        (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))))⁻¹ := by
  have hspec0 : spectrum ℂ
      (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) = {0} := by
    have h0 : (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
        = (0 : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
      (zero_smul ℂ (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))).symm
    rw [h0]
    exact spectrum_smul_one_eq
  have hres : Ring.inverse (algebraMap ℂ
      (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) 3
      - (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      = (3 : ℂ)⁻¹ • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
    rw [sub_zero, Algebra.algebraMap_eq_smul_one]
    exact ringInverse_smul_one (by norm_num)
  rw [hres, hspec0, Metric.infDist_singleton, dist_eq_norm, norm_smul, norm_one,
    mul_one]
  norm_num

/-- Bauer–Fike on `EuclideanSpace ℂ (Fin 2)`: the perturbation `0 + 1`
moves the spectrum from `{0}` to `{1}`, distance `‖1‖ = 1`. -/
example : Metric.infDist (1 : ℂ) (spectrum ℂ
    (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
    ≤ ‖(1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))‖ := by
  have hmem : (1 : ℂ) ∈ spectrum ℂ
      ((0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
        + (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) := by
    rw [zero_add]
    have h1 : (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
        = (1 : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
      simp
    rw [h1]
    exact (mem_spectrum_smul_one_iff).mpr rfl
  exact infDist_le_norm_of_mem_spectrum_add hmem

#print axioms MathlibExt.Analysis.InnerProductSpace.BauerFike.norm_ringInverse_sub_smul_one_le
#print axioms MathlibExt.Analysis.InnerProductSpace.BauerFike.infDist_le_norm_of_mem_spectrum_add
#print axioms MathlibExt.Analysis.InnerProductSpace.BauerFike.exists_mem_spectrum_norm_sub_le
#print axioms MathlibExt.Analysis.InnerProductSpace.BauerFike.hausdorffDist_spectrum_le_of_isSelfAdjoint

end MathlibExtTest.Analysis.InnerProductSpace.BauerFikeTests
