/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Inequalities.OSSS
import Code.OSSS.CovLowerBound

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.CovLowerBound

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {ν : E → Bool → ℝ}














theorem oc2_cov_frame (ν : E → Bool → ℝ) (F G : ConfigSpace E → ℝ) :
    cov ν F G = expect ν (fun ω => F ω * G ω) - expect ν F * expect ν G := rfl


theorem oc2_cov_frame_comm (ν : E → Bool → ℝ) (F G : ConfigSpace E → ℝ) :
    cov ν F G = cov ν G F := cov_comm ν F G



theorem oc2_cov_frame_const_left (hν : IsProbWeight ν) (c : ℝ) (G : ConfigSpace E → ℝ) :
    cov ν (fun _ => c) G = 0 := cov_const hν c G



theorem oc2_cov_frame_const_right (hν : IsProbWeight ν) (c : ℝ) (F : ConfigSpace E → ℝ) :
    cov ν F (fun _ => c) = 0 := by
  rw [oc2_cov_frame_comm]; exact cov_const hν c F











theorem oc2_cov_coordI_frame (ν : E → Bool → ℝ) (e : E) (f : ConfigSpace E → ℝ) :
    cov ν (coordI e) f
      = expect ν (fun ω => coordI e ω * f ω)
          - expect ν (coordI e) * expect ν f := rfl










theorem oc2_expect_coordI (hν : IsProbWeight ν) (e : E) :
    expect ν (coordI e) = ν e true := by
  
  rw [expect_cond ν e (coordI e)]
  
  have htrue : expect (Function.update ν e (pt true)) (coordI e)
      = expect (Function.update ν e (pt true)) (fun _ => (1 : ℝ)) := by
    unfold OSSS.expect
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : ω e = true
    · simp only [coordI, hω, if_true]
    · 
      have hwzero : weight (Function.update ν e (pt true)) ω = 0 := by
        rw [weight_cond ν e true ω]
        have : pt true (ω e) = 0 := by
          simp only [pt]; rw [if_neg]; exact fun h => hω (by rw [h])
        rw [this]; ring
      rw [hwzero]; ring
  have hfalse : expect (Function.update ν e (pt false)) (coordI e) = 0 := by
    unfold OSSS.expect
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : ω e = true
    · 
      have hwzero : weight (Function.update ν e (pt false)) ω = 0 := by
        rw [weight_cond ν e false ω]
        have : pt false (ω e) = 0 := by
          simp only [pt]; rw [if_neg]; rw [hω]; exact fun h => by simp at h
        rw [this]; ring
      rw [hwzero]; ring
    · have hωf : ω e = false := Bool.not_eq_true _ ▸ hω
      simp only [coordI, hωf, Bool.false_eq_true, if_false, mul_zero]
  rw [htrue, hfalse, expect_one (isProbWeight_cond hν e true), mul_one, mul_zero, add_zero]









theorem oc2_cov_coordI_bernoulli (hν : IsProbWeight ν) (e : E) (f : ConfigSpace E → ℝ) :
    cov ν (coordI e) f
      = expect ν (fun ω => coordI e ω * f ω) - ν e true * expect ν f := by
  rw [oc2_cov_coordI_frame, oc2_expect_coordI hν]







theorem oc2_cov_frame_add_right (ν : E → Bool → ℝ) (F G H : ConfigSpace E → ℝ) :
    cov ν F (fun ω => G ω + H ω) = cov ν F G + cov ν F H := by
  unfold cov
  rw [show (fun ω => F ω * (G ω + H ω)) = (fun ω => F ω * G ω + F ω * H ω) from by
        funext ω; ring,
      expect_add, expect_add]
  ring


theorem oc2_cov_frame_add_left (ν : E → Bool → ℝ) (F G H : ConfigSpace E → ℝ) :
    cov ν (fun ω => F ω + G ω) H = cov ν F H + cov ν G H := by
  rw [oc2_cov_frame_comm, oc2_cov_frame_add_right, oc2_cov_frame_comm ν H F,
    oc2_cov_frame_comm ν H G]


theorem oc2_cov_frame_smul_right (ν : E → Bool → ℝ) (c : ℝ) (F G : ConfigSpace E → ℝ) :
    cov ν F (fun ω => c * G ω) = c * cov ν F G := by
  unfold cov
  rw [show (fun ω => F ω * (c * G ω)) = (fun ω => c * (F ω * G ω)) from by funext ω; ring,
      expect_const_mul, expect_const_mul]
  ring


theorem oc2_cov_frame_smul_left (ν : E → Bool → ℝ) (c : ℝ) (F G : ConfigSpace E → ℝ) :
    cov ν (fun ω => c * F ω) G = c * cov ν F G := by
  rw [oc2_cov_frame_comm, oc2_cov_frame_smul_right, oc2_cov_frame_comm ν G F]








theorem oc2_var_frame (ν : E → Bool → ℝ) (F : ConfigSpace E → ℝ) :
    var ν F = expect ν (fun ω => F ω * F ω) - expect ν F * expect ν F := rfl







theorem oc2_var_indicator (A : Set (ConfigSpace E)) :
    var ν (A.indicator (fun _ => (1 : ℝ)))
      = expect ν (A.indicator (fun _ => (1 : ℝ)))
          * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))) := by
  rw [oc2_var_frame]
  have hidem : (fun ω => (A.indicator (fun _ => (1 : ℝ))) ω * (A.indicator (fun _ => (1 : ℝ))) ω)
      = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]; ring
    · rw [Set.indicator_of_notMem hω]; ring
  rw [hidem]; ring













def oc2_CovProductFrame (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) (θ covCorr : ℝ) : Prop :=
  covCorr = ∑ e, cov ν (coordI e) f ∧ θ = expect ν f





theorem oc2_corOSSS_RHS_frame (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) :
    oc2_CovProductFrame ν f (expect ν f) (∑ e, cov ν (coordI e) f) :=
  ⟨rfl, rfl⟩









theorem oc2_covProductFrame_sum_frame (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) :
    (∑ e, cov ν (coordI e) f)
      = ∑ e, (expect ν (fun ω => coordI e ω * f ω) - expect ν (coordI e) * expect ν f) :=
  Finset.sum_congr rfl (fun e _ => oc2_cov_coordI_frame ν e f)






theorem oc2_covProductFrame_sum_bernoulli (hν : IsProbWeight ν) (f : ConfigSpace E → ℝ) :
    (∑ e, cov ν (coordI e) f)
      = ∑ e, (expect ν (fun ω => coordI e ω * f ω) - ν e true * expect ν f) :=
  Finset.sum_congr rfl (fun e _ => oc2_cov_coordI_bernoulli hν e f)

end Walls
end StatMech
