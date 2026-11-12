/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ConsumptionSDF
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! # Tests for `MathlibExt.Probability.Finance.ConsumptionSDF` -/

open MathlibExt.Probability.Finance.ConsumptionSDF

namespace MathlibExtTest.ConsumptionSDF

theorem hasDerivAt_quadratic (c : ℝ) :
    HasDerivAt (fun c : ℝ => c - c ^ 2 / 4) (1 - c / 2) c := by
  have hpow : HasDerivAt (fun c : ℝ => c ^ 2) (2 * c) c := by
    have h2 : HasDerivAt ((fun x : ℝ => x) * (fun x : ℝ => x)) (1 * c + c * 1) c :=
      (hasDerivAt_id' c).mul (hasDerivAt_id' c)
    have hfun : ((fun x : ℝ => x) * (fun x : ℝ => x)) = (fun c : ℝ => c ^ 2) := by
      ext x
      simp [sq]
    have hderiv : (1 : ℝ) * c + c * 1 = 2 * c := by ring
    rw [hfun, hderiv] at h2
    exact h2
  have hdiv : HasDerivAt (fun c : ℝ => c ^ 2 / 4) (2 * c / 4) c := hpow.div_const 4
  have h := (hasDerivAt_id' c).sub hdiv
  have hderiv : (1 : ℝ) - c / 2 = 1 - 2 * c / 4 := by ring
  rw [hderiv]
  exact h

theorem deriv_quadratic (c : ℝ) :
    deriv (fun c : ℝ => c - c ^ 2 / 4) c = 1 - c / 2 :=
  (hasDerivAt_quadratic c).deriv

theorem isLocalMax_expectedUtility_quadratic : IsLocalMax
    (expectedUtility (fun c : ℝ => c - c ^ 2 / 4) (1/2) ![1/2, 1/2] 1 (1/2) ![1, 1]
      ![2, 0]) 0 := by
  have hmaxon : IsMaxOn
      (expectedUtility (fun c : ℝ => c - c ^ 2 / 4) (1/2) ![1/2, 1/2] 1 (1/2) ![1, 1]
        ![2, 0]) Set.univ 0 := by
    rw [isMaxOn_iff]
    intro ξ _
    simp only [expectedUtility, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith [sq_nonneg ξ]
  exact hmaxon.isLocalMax Filter.univ_mem

example : IsLocalMax
    (expectedUtility (fun c : ℝ => c - c ^ 2 / 4) (1/2) ![1/2, 1/2] 1 (1/2) ![1, 1]
      ![2, 0]) 0 :=
  isLocalMax_expectedUtility_quadratic

example : (1/2 : ℝ) = ∑ ω, ![1/2, 1/2] ω *
    (marginalUtilitySDF (fun c : ℝ => c - c ^ 2 / 4) (1/2) (1 - 0 * (1/2))
      (fun ω => ![1, 1] ω + 0 * ![2, 0] ω) ω * ![2, 0] ω) := by
  have h0 : DifferentiableAt ℝ (fun c : ℝ => c - c ^ 2 / 4) (1 - 0 * (1/2)) :=
    (hasDerivAt_quadratic _).differentiableAt
  have h1 : ∀ ω : Fin 2, DifferentiableAt ℝ (fun c : ℝ => c - c ^ 2 / 4)
      (![1, 1] ω + 0 * ![2, 0] ω) :=
    fun ω => (hasDerivAt_quadratic _).differentiableAt
  have hmu : deriv (fun c : ℝ => c - c ^ 2 / 4) (1 - 0 * (1/2)) ≠ 0 := by
    rw [deriv_quadratic]
    norm_num
  exact price_eq_sum_marginalUtilitySDF_mul h0 h1 hmu isLocalMax_expectedUtility_quadratic

example : marginalUtilitySDF (fun c : ℝ => c - c ^ 2 / 4) (1/2) 1
    (fun _ : Fin 2 => (1 : ℝ)) 0 = 1/2 := by
  simp only [marginalUtilitySDF, deriv_quadratic]
  norm_num

example : ∀ ω : Fin 2, 0 < ![1/2, 1/2] ω *
    marginalUtilitySDF (fun c : ℝ => c - c ^ 2 / 4) (1/2) 1
      (fun _ : Fin 2 => (1 : ℝ)) ω := by
  have hπ : ∀ ω : Fin 2, (0 : ℝ) < ![1/2, 1/2] ω := by
    rw [Fin.forall_fin_two]
    constructor <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  have hu0 : 0 < deriv (fun c : ℝ => c - c ^ 2 / 4) 1 := by
    rw [deriv_quadratic]
    norm_num
  have hu1 : ∀ ω : Fin 2,
      0 < deriv (fun c : ℝ => c - c ^ 2 / 4) ((fun _ : Fin 2 => (1 : ℝ)) ω) := by
    intro ω
    simpa using hu0
  intro ω
  exact mul_marginalUtilitySDF_pos (show (0 : ℝ) < 1/2 by norm_num) hπ hu0 hu1 ω

end MathlibExtTest.ConsumptionSDF
