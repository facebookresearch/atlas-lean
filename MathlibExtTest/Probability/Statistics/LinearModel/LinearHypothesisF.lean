/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesisF

/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.LinearHypothesisF`

The `F(1, 1)` specialization is a direct instance of the linear-hypothesis `F` law.
A rank-deficient design is excluded, and chi-square with zero degrees of freedom is
not a Dirac mass.
-/

namespace MathlibExt.Probability.Statistics.LinearModel.FStatChecks

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- Use case: the `F(1, 1)` specialization is a direct instance of the pinned law. -/
example {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    [Fintype r] [DecidableEq r] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ))
    (hr : Fintype.card r = 1) (hkm : Fintype.card m = Fintype.card k + 1)
    (β : k → ℝ) {c : r → ℝ} (hβ : C *ᵥ β = c) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => fStatistic X C c (X *ᵥ β + ε ω))
      (snedecorFMeasure 1 1) μ := by
  have hr' : 0 < Fintype.card r := by omega
  have hkm' : Fintype.card k < Fintype.card m := by omega
  have h2 : Fintype.card m - Fintype.card k = 1 := by omega
  have h := hasLaw_fStatistic hX hC hr' hkm' β hβ hσ hε
  rwa [hr, h2] at h

/-- Boundary: a rank-deficient design (two equal columns) is excluded. -/
example : ¬ IsUnit ((Matrix.of fun (_ : Fin 3) (_ : Fin 2) => (1 : ℝ))ᵀ *
    Matrix.of fun (_ : Fin 3) (_ : Fin 2) => (1 : ℝ)) := by
  intro h
  rw [Matrix.isUnit_iff_isUnit_det] at h
  have hmat : (Matrix.of fun (_ : Fin 3) (_ : Fin 2) => (1 : ℝ))ᵀ *
      (Matrix.of fun (_ : Fin 3) (_ : Fin 2) => (1 : ℝ)) = !![3, 3; 3, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  rw [hmat, Matrix.det_fin_two] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  norm_num at h

/-- Degenerate endpoint: chi-square with zero degrees of freedom is not a Dirac mass,
which is why the `0 < q` and `p < n` hypotheses cannot be dropped. -/
example : chiSquareMeasure 0 ≠ Measure.dirac (0 : ℝ) := by
  have hac : chiSquareMeasure 0 ≪ (volume : Measure ℝ) :=
    withDensity_absolutelyContinuous _ _
  have h0 : chiSquareMeasure 0 ({0} : Set ℝ) = 0 := hac Real.volume_singleton
  have hd : Measure.dirac (0 : ℝ) ({0} : Set ℝ) = 1 := by simp
  intro h
  rw [h] at h0
  rw [hd] at h0
  exact one_ne_zero h0

end MathlibExt.Probability.Statistics.LinearModel.FStatChecks
