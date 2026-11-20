/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic





open Finset

namespace StatMech.FrontierA

noncomputable section


def hadamardQuadraticFactor (r : Real) (z : ℂ) : ℂ :=
  1 + (r : ℂ) * z ^ 2

theorem analyticAt_hadamardQuadraticFactor (r : Real) (z : ℂ) :
    AnalyticAt ℂ (hadamardQuadraticFactor r) z := by
  unfold hadamardQuadraticFactor
  fun_prop

theorem hasDerivAt_hadamardQuadraticFactor (r : Real) (z : ℂ) :
    HasDerivAt (hadamardQuadraticFactor r) (2 * (r : ℂ) * z) z := by
  have h := (hasDerivAt_const z (1 : ℂ)).add
    (((hasDerivAt_id z).pow 2).const_mul (r : ℂ))
  convert h using 1 <;> simp [id] <;> ring


theorem analyticOrderAt_hadamardQuadraticFactor_eq_one_of_zero
    {r : Real} (hr : 0 < r) {z : ℂ}
    (hz : hadamardQuadraticFactor r z = 0) :
    analyticOrderAt (hadamardQuadraticFactor r) z = 1 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp [hadamardQuadraticFactor] at hz
  have hf := analyticAt_hadamardQuadraticFactor r z
  apply hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
  rw [(hasDerivAt_hadamardQuadraticFactor r z).deriv]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hr0) hz0


theorem analyticOrderAt_hadamardQuadraticFactor_eq_zero_of_ne
    {r : Real} {z : ℂ} (hz : hadamardQuadraticFactor r z ≠ 0) :
    analyticOrderAt (hadamardQuadraticFactor r) z = 0 :=
  (analyticAt_hadamardQuadraticFactor r z).analyticOrderAt_eq_zero.mpr hz

theorem analyticOrderAt_hadamardQuadraticFactor_eq_ite
    {r : Real} (hr : 0 < r) (z : ℂ) :
    analyticOrderAt (hadamardQuadraticFactor r) z =
      if hadamardQuadraticFactor r z = 0 then 1 else 0 := by
  split
  · exact analyticOrderAt_hadamardQuadraticFactor_eq_one_of_zero hr ‹_›
  · exact analyticOrderAt_hadamardQuadraticFactor_eq_zero_of_ne ‹_›



theorem analyticOrderAt_finset_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z) :
    analyticOrderAt (fun w => ∏ i ∈ s, f i w) z =
      ∑ i ∈ s, analyticOrderAt (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [analyticOrderAt_eq_zero]
  | @insert a s ha ih =>
      have hfa : AnalyticAt ℂ (f a) z := hf a (mem_insert_self a s)
      have hfs : AnalyticAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
        have hfun : (fun w => ∏ i ∈ s, f i w) = ∏ i ∈ s, f i := by
          funext w
          simp
        rw [hfun]
        exact Finset.analyticAt_prod s
          (fun i hi => hf i (mem_insert_of_mem hi))
      rw [sum_insert ha]
      have hprod : (fun w => ∏ i ∈ insert a s, f i w) =
          fun w => f a w * ∏ i ∈ s, f i w := by
        funext w
        rw [prod_insert ha]
      rw [hprod]
      change analyticOrderAt
          ((f a) • (fun w => ∏ i ∈ s, f i w)) z = _
      rw [analyticOrderAt_smul hfa hfs]
      congr 1
      exact ih (fun i hi => hf i (mem_insert_of_mem hi))



theorem analyticOrderAt_hadamardQuadraticFactor_prod
    {ι : Type*} (s : Finset ι) (r : ι → Real)
    (hr : ∀ i ∈ s, 0 < r i) (z : ℂ) :
    analyticOrderAt (fun w => ∏ i ∈ s, hadamardQuadraticFactor (r i) w) z =
      (#{i ∈ s | hadamardQuadraticFactor (r i) z = 0} : Nat) := by
  classical
  rw [analyticOrderAt_finset_prod s
    (fun i => hadamardQuadraticFactor (r i)) z
    (fun i _ => analyticAt_hadamardQuadraticFactor (r i) z)]
  calc
    (∑ i ∈ s, analyticOrderAt (hadamardQuadraticFactor (r i)) z) =
        ∑ i ∈ s, if hadamardQuadraticFactor (r i) z = 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact analyticOrderAt_hadamardQuadraticFactor_eq_ite (hr i hi) z
    _ = (#{i ∈ s | hadamardQuadraticFactor (r i) z = 0} : Nat) := by
      exact Finset.sum_boole _ _

end

end StatMech.FrontierA
