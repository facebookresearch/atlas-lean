/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Navigation.ObservationPorts
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stacked GNSS observation checks

Concrete consumer of `PhyslibExt.Navigation.ObservationPorts`: the
observation operator on nonzero position and clock directions, the
stacked pseudorange derivative along the first axis, the unique state
correction of one residual vector, and the two boundaries: a receiver
at a satellite has no derivative row, and a repeated satellite gives
a singular operator with a nonzero invisible direction. For the frozen
surrogate: a product model meeting every measure premise, the posterior
there with a nondegenerate prior and positive measurement noise, the
positive semidefinite branch where `step_valid` does not apply, and
shared noise violating the independence premise.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the operator
with a repeated satellite that its last example checks. Section B
defines the product model of the three Gaussian laws and proves that it
meets the measure premises.

## iii. Table of contents

- A. Directions, corrections and boundaries
- B. The frozen linear surrogate

## iv. References

- `PhyslibExt.Navigation.ObservationPorts`
-/

namespace PhyslibExtTest.Navigation.ObservationPorts

open _root_.Navigation.ObservationPorts
open scoped InnerProductSpace Matrix

/-! ## A. Directions, corrections and boundaries -/

/-- Nonzero directions: the position direction `e₁` gives `(1, 0, 0, -1)`, the pure clock rate
gives the common mode `(1, 1, 1, 1)`, and the mixed direction `(1, 2, 3, 4)` gives
`(5, 6, 7, 3)`. -/
example :
    observationMatrix *ᵥ stateDirection (EuclideanSpace.single 0 1) 0 = ![1, 0, 0, -1] ∧
      observationMatrix *ᵥ stateDirection 0 1 = ![1, 1, 1, 1] ∧
      observationMatrix *ᵥ ![1, 2, 3, 4] = ![5, 6, 7, 3] := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [observationMatrix, stateDirection, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_four]
  · funext i
    fin_cases i <;> simp [observationMatrix, stateDirection, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_four]
  · funext i
    fin_cases i <;> simp [observationMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four] <;> ring

/-- A receiver coinciding with a satellite is rejected: for `d ≠ 0` the pseudorange
`‖s + t • d - s‖ + (b₀ + t * db)` is not differentiable at `t = 0`. -/
example (s d : EuclideanSpace ℝ (Fin 3)) (hd : d ≠ 0)
    (b₀ db : ℝ) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => ‖s + t • d - s‖ + (b₀ + t * db)) 0 := by
  have hclock : DifferentiableAt ℝ (fun t : ℝ => b₀ + t * db) 0 :=
    ((hasDerivAt_const_add_iff b₀).mpr (hasDerivAt_mul_const db)).differentiableAt
  intro h
  have hnorm : DifferentiableAt ℝ (fun t : ℝ => ‖s + t • d - s‖) 0 := by
    have hsub := h.sub hclock
    have hfun : (fun t : ℝ => ‖s + t • d - s‖ + (b₀ + t * db)) - (fun t : ℝ => b₀ + t * db) =
        (fun t : ℝ => ‖s + t • d - s‖) := by
      ext t
      simp
    rwa [hfun] at hsub
  have hsmul : DifferentiableAt ℝ (fun t : ℝ => ‖t • d‖) 0 := by
    have hfun : (fun t : ℝ => ‖s + t • d - s‖) = (fun t : ℝ => ‖t • d‖) := by
      ext t
      congr 1
      abel
    rwa [hfun] at hnorm
  have hC : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have habsC : DifferentiableAt ℝ (fun t : ℝ => |t| * ‖d‖) 0 := by
    have hfun : (fun t : ℝ => ‖t • d‖) = (fun t : ℝ => |t| * ‖d‖) := by
      ext t
      rw [norm_smul, Real.norm_eq_abs]
    rwa [hfun] at hsmul
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    have hdiv := habsC.div_const (‖d‖)
    have hfun : (fun t : ℝ => |t| * ‖d‖ / ‖d‖) = (fun t : ℝ => |t|) := by
      ext t
      field_simp
    rwa [hfun] at hdiv
  exact not_differentiableAt_abs_zero habs

/-- The rows obtained when the fourth satellite repeats the first, at `-e₁`. -/
def repeatedObservationMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1; 1, 0, 0, 1]

/-- Repeated rows give rank failure: determinant `0`, and the nonzero direction
`(1, 1, 1, -1)` is mapped to `0`. -/
example :
    repeatedObservationMatrix.det = 0 ∧
      repeatedObservationMatrix *ᵥ ![1, 1, 1, -1] = 0 ∧
      ¬ Function.Injective repeatedObservationMatrix.mulVec := by
  have hker : repeatedObservationMatrix *ᵥ ![1, 1, 1, -1] = 0 := by
    funext i
    fin_cases i <;> simp [repeatedObservationMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
  have hdet : repeatedObservationMatrix.det = 0 := by
    have h30 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 := rfl
    have h31 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := rfl
    have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp [repeatedObservationMatrix]
    rw [Matrix.det_fin_three, Matrix.det_fin_three]
    simp [Matrix.submatrix_apply, h30, h31, h32]
    ring
  refine ⟨hdet, hker, ?_⟩
  intro hinj
  have h2 : ![1, 1, 1, -1] = (0 : Fin 4 → ℝ) := hinj (by rw [hker, Matrix.mulVec_zero])
  have h3 := congrFun h2 0
  simp at h3

/-- The stacked pseudorange derivative along the first axis, with zero clock rate, is
`(1, 0, 0, -1)`: the two satellites on that axis see the receiver move toward one and away from
the other, and the others see no change to first order. -/
example (b₀ : ℝ) :
    HasDerivAt (stackedPseudorange (EuclideanSpace.single 0 1) b₀ 0) ![1, 0, 0, -1] 0 := by
  have hv : observationMatrix *ᵥ stateDirection (EuclideanSpace.single 0 1) 0 = ![1, 0, 0, -1] := by
    funext i
    fin_cases i <;> simp [observationMatrix, stateDirection, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_four]
  have h := stackedPseudorange_hasDerivAt (EuclideanSpace.single 0 1) b₀ 0
  rwa [hv] at h

/-- The residual `(5, 6, 7, 3)` has exactly one state correction, `(1, 2, 3, 4)`. -/
example :
    (∃! v : Fin 4 → ℝ, observationMatrix *ᵥ v = ![5, 6, 7, 3]) ∧
      ∀ v : Fin 4 → ℝ, observationMatrix *ᵥ v = ![5, 6, 7, 3] → v = ![1, 2, 3, 4] := by
  have h1234 : observationMatrix *ᵥ ![1, 2, 3, 4] = ![5, 6, 7, 3] := by
    funext i
    fin_cases i <;> simp [observationMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four] <;>
      ring
  exact ⟨observationMatrix_existsUnique _,
    fun v hv => observationMatrix_mulVec_injective (hv.trans h1234.symm)⟩

/-- The receiver differs from each satellite, and the determinant is `2`. -/
example : (∀ j, (0 : EuclideanSpace ℝ (Fin 3)) ≠ satellite j) ∧ observationMatrix.det = 2 :=
  ⟨satellite_ne_receiver, observationMatrix_det⟩

/-! ## B. The frozen linear surrogate -/

open MeasureTheory ProbabilityTheory Matrix WithLp
open Cslib.MachineLearning.Sequence.KalmanFilter (Belief predict step)

/-- The product model: prior state, process noise and measurement noise drawn independently from
`N(m, P)`, `N(0, Q)` and `N(0, R)` on `(ℝ⁴ × ℝ⁴) × ℝ⁴`. -/
noncomputable def productModel (b : Belief (Fin 4)) (Q R : Matrix (Fin 4) (Fin 4) ℝ) :
    Measure ((EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) × EuclideanSpace ℝ (Fin 4)) :=
  ((multivariateGaussian b.mean b.cov).prod (multivariateGaussian 0 Q)).prod
    (multivariateGaussian 0 R)

/-- The product model is a probability measure. -/
instance (b : Belief (Fin 4)) (Q R : Matrix (Fin 4) (Fin 4) ℝ) :
    IsProbabilityMeasure (productModel b Q R) := by
  unfold productModel
  infer_instance

/-- The product model meets every measure premise of the posterior: its coordinates
`X0 = ω.1.1`, `w = ω.1.2`, `v = ω.2` satisfy both independence premises, and their laws are
`N(m, P)`, `N(0, Q)` and `N(0, R)`. -/
lemma productModel_premises (b : Belief (Fin 4)) (Q R : Matrix (Fin 4) (Fin 4) ℝ) :
    IndepFun (fun ω => ω.1.1) (fun ω => ω.1.2) (productModel b Q R) ∧
      IndepFun (fun ω => (ω.1.1, ω.1.2)) (fun ω => ω.2) (productModel b Q R) ∧
      (productModel b Q R).map (fun ω => ω.1.1) = b.law ∧
      (productModel b Q R).map (fun ω => ω.1.2) = multivariateGaussian 0 Q ∧
      (productModel b Q R).map (fun ω => ω.2) = multivariateGaussian 0 R := by
  set A := multivariateGaussian b.mean b.cov with hA
  set B := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 4)) Q with hB
  set C := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 4)) R with hC
  have hμ : productModel b Q R = (A.prod B).prod C := rfl
  rw [hμ]
  have hfst : ((A.prod B).prod C).map Prod.fst = A.prod B := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h11 : ((A.prod B).prod C).map (fun ω => ω.1.1) = A := by
    rw [show (fun ω : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ×
        EuclideanSpace ℝ (Fin 4) => ω.1.1) = Prod.fst ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_fst measurable_fst, hfst, Measure.map_fst_prod, measure_univ,
      one_smul]
  have h12 : ((A.prod B).prod C).map (fun ω => ω.1.2) = B := by
    rw [show (fun ω : (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) ×
        EuclideanSpace ℝ (Fin 4) => ω.1.2) = Prod.snd ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_snd measurable_fst, hfst, Measure.map_snd_prod, measure_univ,
      one_smul]
  have h2 : ((A.prod B).prod C).map (fun ω => ω.2) = C := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨?_, ?_, h11, h12, h2⟩
  · refine (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr ?_
    rw [h11, h12]
    exact hfst
  · exact indepFun_prod (μ := A.prod B) (ν := C) measurable_id measurable_id

/-- Nonzero positive measurement noise and a nondegenerate prior: in the product model with prior
`N(0, I)`, `F = I`, `Q = I` and `R = I`, the conditional law of `X1` given `Y` is the Kalman step
for almost every observation. -/
example :
    ∀ᵐ y ∂(productModel ⟨0, 1⟩ 1 1).map
        (surrogateObservation 1 (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2)),
      condDistrib (predictedState 1 (fun ω => ω.1.1) (fun ω => ω.1.2))
          (surrogateObservation 1 (fun ω => ω.1.1) (fun ω => ω.1.2) (fun ω => ω.2))
          (productModel ⟨0, 1⟩ 1 1) y =
        (step 1 1 observationMatrix 1 y ⟨0, 1⟩).law := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := productModel_premises ⟨0, 1⟩ 1 1
  have hC : (predict 1 1 (⟨0, 1⟩ : Belief (Fin 4))).cov.PosSemidef :=
    Cslib.MachineLearning.Sequence.KalmanFilter.predict_valid 1 1 PosSemidef.one PosSemidef.one
  exact condDistrib_predictedState_surrogateObservation measurable_fst.fst measurable_fst.snd
    measurable_snd h1 h2 PosSemidef.one PosSemidef.one PosSemidef.one h3 h4 h5 1
    (innovation_isUnit_of_posDef hC PosDef.one)

/-- The positive semidefinite branch without `step_valid`: for prior covariance `I`, `F = I` and
`Q = R = 0`, `R` is positive semidefinite and the innovation `H Hᵀ` is invertible
(determinant `4`), so the posterior applies, but `R` is not positive definite, so `step_valid`
cannot be applied from these premises. -/
example {b : Belief (Fin 4)} (hb : b.cov = 1) :
    (0 : Matrix (Fin 4) (Fin 4) ℝ).PosSemidef ∧
      IsUnit (observationMatrix * (predict 1 0 b).cov * observationMatrixᵀ + 0).det ∧
      ¬ (0 : Matrix (Fin 4) (Fin 4) ℝ).PosDef := by
  refine ⟨PosSemidef.zero, ?_, ?_⟩
  · have hcov : (predict 1 0 b).cov = 1 := by
      simp [predict, hb]
    rw [hcov, Matrix.mul_one, add_zero, det_mul, det_transpose, observationMatrix_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · intro h
    have hx : (Finsupp.single (0 : Fin 4) (1 : ℝ)) ≠ 0 := by simp
    have h0 := h.2 hx
    simp at h0

/-- Shared noise in the product model: taking the sensor noise equal to the process noise
`w ~ N(0, I)` violates the second independence premise. -/
example :
    ¬ IndepFun (fun ω => (ω.1.1, ω.1.2)) (fun ω => ω.1.2) (productModel ⟨0, 1⟩ 1 1) :=
  not_indepFun_of_shared_noise measurable_fst.snd PosSemidef.one
    (productModel_premises ⟨0, 1⟩ 1 1).2.2.2.1 (i := 0) (by simp)

end PhyslibExtTest.Navigation.ObservationPorts
