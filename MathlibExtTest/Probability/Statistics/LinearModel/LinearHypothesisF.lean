/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesisF

open Matrix

/-!
# Tests for linear-hypothesis `F` and single-contrast `T ^ 2`

The `F(1, 1)` specialization is a direct instance of the linear-hypothesis `F` law; a
rank-deficient design is excluded; chi-square with zero degrees of freedom is not a Dirac
measure. The intercept design with `n = 2`, `p = 1` gives `F(1, 1)`; a zero contrast has
zero variance factor; the squared `t` statistic agrees pointwise with the rank-one `F`
statistic.
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

namespace ProbabilityTheory

open MeasureTheory Real

private lemma intercept_gram (n : ℕ) :
    (Matrix.of fun (_ : Fin n) (_ : Fin 1) => (1 : ℝ))ᵀ *
        Matrix.of (fun (_ : Fin n) (_ : Fin 1) => (1 : ℝ)) =
      Matrix.of fun _ _ => (n : ℝ) := by
  ext i j
  simp [Matrix.mul_apply]

private lemma intercept_isUnit_gram {n : ℕ} (hn : n ≠ 0) :
    IsUnit ((Matrix.of fun (_ : Fin n) (_ : Fin 1) => (1 : ℝ))ᵀ *
        Matrix.of (fun (_ : Fin n) (_ : Fin 1) => (1 : ℝ))) := by
  rw [Matrix.isUnit_iff_isUnit_det, intercept_gram, Matrix.det_unique]
  simpa using hn

end ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory

private theorem tsq_contrastVariance_zero {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] (X : Matrix m k ℝ) : contrastVariance X 0 = 0 := by
  classical
  simp [contrastVariance, dotProduct]

end MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExt.Probability.Statistics.LinearModel.TSqChecks

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

/-- Use case: intercept design with `n = 2`, `p = 1` (positive residual df) gives
`F(1, 1)` law. -/
example {σ : ℝ} (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    HasLaw (fun x : Fin 2 → ℝ => (tStatistic
        (Matrix.of fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ)) (fun _ => 1) β
        ((Matrix.of fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ)) *ᵥ β + σ • x)) ^ 2)
      (snedecorFMeasure 1 (Fintype.card (Fin 2) - Fintype.card (Fin 1)))
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  have hX : IsUnit ((Matrix.of fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))ᵀ *
      (Matrix.of fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))) :=
    ProbabilityTheory.intercept_isUnit_gram (by norm_num)
  have hsmul : (fun x : Fin 2 → ℝ => σ⁻¹ • (σ • x)) = id := by
    funext x
    simp [smul_smul, inv_mul_cancel₀ hσ.ne']
  have hε : HasLaw (fun x : Fin 2 → ℝ => σ⁻¹ • (σ • x))
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    rw [hsmul]
    exact ⟨measurable_id.aemeasurable, MeasureTheory.Measure.map_id⟩
  exact hasLaw_tStatistic_sq hX (by decide) β hσ hε (fun h => one_ne_zero (congrFun h 0))

/-- Boundary: a zero contrast has zero variance factor, so `a ≠ 0` cannot be dropped. -/
example {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (X : Matrix m k ℝ) : contrastVariance X 0 = 0 := by
  exact tsq_contrastVariance_zero X

/-- Rank-one agreement use case: the `F` statistic of the single-row hypothesis matrix
equals `T ^ 2`, by the production theorem. -/
example {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {X : Matrix m k ℝ} (a β : k → ℝ) (y : m → ℝ) :
    (tStatistic X a β y) ^ 2 =
      fStatistic X (Matrix.of fun _ : Fin 1 => a) (fun _ => a ⬝ᵥ β) y :=
  tStatistic_sq_eq_fStatistic (X := X) a β y

end MathlibExt.Probability.Statistics.LinearModel.TSqChecks
