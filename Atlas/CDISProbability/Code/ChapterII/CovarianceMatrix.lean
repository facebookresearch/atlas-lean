/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# CDIS Probabilités II: mean vector and covariance matrix

* id 39: for a random vector `X = (X_1, ..., X_n)`, the mean vector `E(X) = (E X_1, ..., E X_n)`
  and the covariance matrix `C_X = (Cov(X_i, X_j))_{i,j}`.
* id 40: the covariance matrix is symmetric positive semidefinite, because
  `vᵀ C_X v = Var(Σ v_i X_i) ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace CDIS

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [Fintype ι]

/-- CDIS P.II, id 39: mean vector `(E X_1, ..., E X_n)`. -/
noncomputable def meanVector (X : ι → Ω → ℝ) (P : Measure Ω) : ι → ℝ := fun i ↦ ∫ ω, X i ω ∂P

/-- CDIS P.II, id 39: covariance matrix `(Cov(X_i, X_j))_{i,j}`. -/
noncomputable def covMatrix (X : ι → Ω → ℝ) (P : Measure Ω) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ cov[X i, X j; P]

/-- `vᵀ C_X v = Var(Σ v_i X_i)`. -/
theorem dotProduct_covMatrix_mulVec [IsFiniteMeasure P] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (v : ι → ℝ) :
    v ⬝ᵥ (covMatrix X P *ᵥ v) = Var[fun ω ↦ ∑ i, v i * X i ω; P] := by
  have hvX : ∀ i, MemLp (fun ω ↦ v i * X i ω) 2 P := fun i ↦ (hX i).const_mul (v i)
  have hsum : AEMeasurable (fun ω ↦ ∑ i, v i * X i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i _ ↦ (hvX i).aemeasurable
  rw [← covariance_self hsum, covariance_fun_sum_fun_sum hvX hvX]
  simp only [dotProduct, mulVec, covMatrix, of_apply, covariance_const_mul_left,
    covariance_const_mul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

-- `Matrix.PosSemidef` itself needs `Fintype ι` through `mulVec`, so the instance stays.
set_option linter.unusedFintypeInType false in
/-- CDIS P.II, id 40: the covariance matrix is symmetric positive semidefinite. -/
theorem covMatrix_posSemidef [IsFiniteMeasure P] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P) :
    (covMatrix X P).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v ↦ ?_⟩
  · ext i j
    simp [covMatrix, covariance_comm]
  · rw [star_trivial, dotProduct_covMatrix_mulVec hX]
    exact variance_nonneg _ _

end CDIS
