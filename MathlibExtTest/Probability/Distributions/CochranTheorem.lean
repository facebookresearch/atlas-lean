/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranTheorem

@[expose] public section

open MeasureTheory ProbabilityTheory Module

namespace MathlibExtTest.Probability.Distributions.CochranTheorem

/-- `Z² ~ χ²₁` for a standard normal `Z`. -/
example : (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = chiSquareMeasure 1 :=
  gaussianReal_map_sq

/-- Three independent standard normal coordinates: `Z₀² + Z₂² ~ χ²₂`. -/
example : (Measure.pi fun _ : Fin 3 => gaussianReal 0 1).map
    (fun x => ∑ i ∈ ({0, 2} : Finset (Fin 3)), x i ^ 2) = chiSquareMeasure 2 :=
  pi_gaussianReal_map_sum_sq (s := {0, 2}) ⟨0, by simp⟩

/-- Boundary: with `K = ⊤` the projection is the identity, so `‖Z‖² ~ χ²_n` on `ℝⁿ`. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 3))).map (fun x => ‖x‖ ^ 2) = chiSquareMeasure 3 := by
  have h := stdGaussian_map_norm_sq_starProjection
    (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (by simp)
  have hid : (fun x => ‖(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))).starProjection x‖ ^ 2) =
      fun x => ‖x‖ ^ 2 := by
    funext x
    rw [Submodule.starProjection_eq_self_iff.2 Submodule.mem_top]
  rw [hid] at h
  simpa using h

open Matrix in
/-- Non-vacuity of the matrix form: the identity matrix is symmetric, idempotent and of rank `2`,
and `Zᵀ I Z = Z₀² + Z₁² ~ χ²₂`. -/
example : (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map
    (fun x => x ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x) = chiSquareMeasure 2 := by
  have h := pi_gaussianReal_map_dotProduct_mulVec (A := (1 : Matrix (Fin 2) (Fin 2) ℝ))
    Matrix.isHermitian_one (by simp) (by simp)
  simpa using h

/-- Junk value behind the positivity hypotheses: `χ²₀` is the zero measure (Mathlib's
`Γ(0) = 0`), not the Dirac mass at `0`, so `K = ⊥` or a zero matrix is excluded. -/
example : chiSquareMeasure 0 = 0 := by
  have h : gammaPDF 0 2⁻¹ = 0 := by
    funext x
    simp [gammaPDF, gammaPDFReal, Real.Gamma_zero]
  simp [chiSquareMeasure, gammaMeasure, h]

end MathlibExtTest.Probability.Distributions.CochranTheorem
