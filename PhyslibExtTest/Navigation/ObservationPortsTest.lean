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
import Mathlib.Tactic.Ring

/-!
# Stacked GNSS observation checks

Concrete consumer of `PhyslibExt.Navigation.ObservationPorts`: the
observation operator on nonzero position and clock directions, the
stacked pseudorange derivative along the first axis, the unique state
correction of one residual vector, and the two boundaries: a receiver
at a satellite has no derivative row, and a repeated satellite gives
a singular operator with a nonzero invisible direction.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the operator
with a repeated satellite that its last example checks.

## iii. Table of contents

- A. Directions, corrections and boundaries

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

end PhyslibExtTest.Navigation.ObservationPorts
