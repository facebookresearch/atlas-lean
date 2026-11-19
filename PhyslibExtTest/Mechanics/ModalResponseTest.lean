/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ModalResponse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Modal response checks

Concrete consumers of `PhyslibExt.Mechanics.ModalResponse`: three unit masses joined pairwise by
unit springs (a ring of three, stiffness eigenvalues `0, 3, 3`), released from a mode of the
repeated eigenvalue with a rigid-translation velocity, and the excluded negative-stiffness branch.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here.

## iii. Table of contents

- A. The ring of three

## iv. References

None.

## A. The ring of three

-/

open Matrix PhyslibExt.Mechanics.ModalResponse

/-- Stiffness matrix of three unit masses joined pairwise by unit springs (a ring of three). -/
def ringStiffness : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, -1, -1; -1, 2, -1; -1, -1, 2]

/-- The ring of three: `ringStiffness` is positive semidefinite, the rigid translation
`(1, 1, 1)` spans its zero modes, `(1, -1, 0)` and `(1, 1, -2)` are two independent modes of the
repeated eigenvalue `3`, and with the unit mass matrix a modal basis exists. -/
example :
    ringStiffness.PosSemidef ∧ ringStiffness *ᵥ ![1, 1, 1] = 0 ∧
      ringStiffness *ᵥ ![1, -1, 0] = (3 : ℝ) • ![1, -1, 0] ∧
      ringStiffness *ᵥ ![1, 1, -2] = (3 : ℝ) • ![1, 1, -2] ∧
      ∃ (C : Matrix (Fin 3) (Fin 3) ℝ) (μ : Fin 3 → ℝ), Cᵀ * 1 * C = 1 ∧
        Cᵀ * ringStiffness * C = diagonal μ ∧ ∀ i, 0 ≤ μ i := by
  have hpsd : ringStiffness.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ringStiffness]
    · simp [ringStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 - x 2)]
  refine ⟨hpsd, ?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [ringStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  · ext i
    fin_cases i <;> simp [ringStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  · ext i
    fin_cases i <;> simp [ringStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  · obtain ⟨C, -, hMC, μ, hKC, hμ⟩ := exists_modalBasis (M := 1) Matrix.PosDef.one hpsd
    exact ⟨C, μ, hMC, hKC, hμ⟩

/-- Repeated positive eigenvalue and initial velocity in the zero eigenspace: for every modal
basis of the ring, the response from `x₀ = (1, -1, 0)` (a mode of the eigenvalue `3`) with
`v₀ = (1, 1, 1)` (rigid translation) is `cos (√3 t) (1, -1, 0) + t (1, 1, 1)`; the rigid drift is
kept. -/
example (C : Matrix (Fin 3) (Fin 3) ℝ) (μ : Fin 3 → ℝ)
    (hMC : Cᵀ * 1 * C = 1) (hKC : Cᵀ * ringStiffness * C = diagonal μ) (hμ : ∀ i, 0 ≤ μ i) :
    modalResponse C μ ![1, -1, 0] ![1, 1, 1] =
      fun t => Real.cos (Real.sqrt 3 * t) • ![1, -1, 0] + t • ![1, 1, 1] := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set w := Real.sqrt 3 with hw
  set a : Fin 3 → ℝ := ![1, -1, 0] with ha
  set b : Fin 3 → ℝ := ![1, 1, 1] with hb
  set y : ℝ → Fin 3 → ℝ := fun t => Real.cos (w * t) • a + t • b with hy
  have h1 : ∀ t : ℝ, HasDerivAt (fun s => w * s) w t := fun t => by
    simpa using (hasDerivAt_id t).const_mul w
  have hyd : ∀ t, HasDerivAt y ((-Real.sin (w * t) * w) • a + (1 : ℝ) • b) t := by
    intro t
    exact (((Real.hasDerivAt_cos (w * t)).comp t (h1 t)).smul_const a).add
      ((hasDerivAt_id t).smul_const b)
  have hydd : ∀ t, HasDerivAt (fun t => (-Real.sin (w * t) * w) • a + (1 : ℝ) • b)
      ((-(Real.cos (w * t) * w) * w) • a) t := by
    intro t
    have h := ((((Real.hasDerivAt_sin (w * t)).comp t (h1 t)).neg.mul_const w).smul_const
      a).add_const ((1 : ℝ) • b)
    exact h.congr_deriv (by simp)
  have hD1 : deriv y = fun t => (-Real.sin (w * t) * w) • a + (1 : ℝ) • b :=
    funext fun t => (hyd t).deriv
  have hyC : ContDiff ℝ 2 y := by
    rw [hy]
    fun_prop
  have hw2 : w * w = 3 := by nlinarith [hs3]
  have hc : ∀ t, -(Real.cos (w * t) * w) * w = -(3 * Real.cos (w * t)) := fun t => by
    linear_combination (-Real.cos (w * t)) * hw2
  have hEq : ∀ t,
      (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ deriv (deriv y) t + ringStiffness *ᵥ y t = 0 := by
    intro t
    rw [hD1, (hydd t).deriv, hc t]
    ext i
    fin_cases i <;> simp [hy, ha, hb, ringStiffness]
      <;> ring
  have hu := modalResponse_unique hMC hKC hμ hyC hEq
  have hy0 : y 0 = a := by
    simp [hy]
  have hyv : deriv y 0 = b := by
    rw [hD1]
    simp
  rw [hy0, hyv] at hu
  exact hu.symm

/-- Negative stiffness needs a different branch: for `μ = -1` the drift formula from rest at
`1` is the constant `1`, which does not solve `q'' - q = 0`. -/
example :
    ¬ ∀ t, deriv (deriv (modalCoordinate (-1) 1 0)) t + (-1) * modalCoordinate (-1) 1 0 t = 0 := by
  intro h
  have hconst : modalCoordinate (-1) 1 0 = fun _ => 1 := by
    funext t
    simp [modalCoordinate]
  have h0 := h 0
  rw [hconst] at h0
  simp at h0
