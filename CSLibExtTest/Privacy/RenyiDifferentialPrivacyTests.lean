/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.RenyiDifferentialPrivacy
public import Cslib.Probability.PMF
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Tests for Rényi differential privacy, finite discrete
-/

@[expose] public section

namespace CSLibExtTest.Privacy.RenyiDifferentialPrivacyTests

open CSLibExt.Privacy.RenyiDifferentialPrivacy

noncomputable def P1 : PMF Bool := PMF.pure true

noncomputable def Q1 : PMF Bool :=
  Cslib.Probability.PMF.uniformOfFintype Bool

theorem test_moment_self : renyiMoment P1 P1 2 = 1 :=
  renyiMoment_self P1 (by norm_num)

theorem test_div_self : renyiDiv P1 P1 2 = 0 :=
  renyiDiv_self P1 (by norm_num)

theorem test_uniform_toReal (w : Bool) :
    (Q1 w).toReal = ((2 : ℕ) : ℝ)⁻¹ := by
  simp [Q1, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool,
    ENNReal.toReal_inv]

theorem test_support : Support P1 Q1 := by
  intro w _ h0
  have h2 := test_uniform_toReal w
  rw [h0, ENNReal.toReal_zero] at h2
  norm_num at h2

theorem test_momentReal_pure_uniform : renyiMomentReal P1 Q1 2 = 2 := by
  have hP1t : (P1 true).toReal = 1 := by simp [P1]
  have hP1f : (P1 false).toReal = 0 := by simp [P1]
  unfold renyiMomentReal
  rw [Fintype.sum_bool]
  simp only [hP1t, hP1f, test_uniform_toReal]
  norm_num [Real.rpow_two, Real.rpow_one]

theorem test_moment_pure_uniform : renyiMoment P1 Q1 2 = 2 := by
  rw [renyiMoment_of_support test_support (by norm_num : (1 : ℝ) < 2),
    test_momentReal_pure_uniform,
    show ((2 : ℝ) : EReal) = 2 from rfl]

theorem test_div_pure_uniform : renyiDiv P1 Q1 2 = (Real.log 2 : EReal) := by
  rw [renyiDiv_of_support test_support (by norm_num : (1 : ℝ) < 2)]
  unfold renyiDivReal
  rw [test_momentReal_pure_uniform, EReal.coe_eq_coe_iff]
  norm_num

theorem test_one_le_moment : 1 ≤ renyiMoment P1 Q1 2 :=
  one_le_renyiMoment P1 Q1 (by norm_num) test_support

theorem test_nonneg_div : 0 ≤ renyiDiv P1 Q1 2 :=
  nonneg_renyiDiv P1 Q1 (by norm_num) test_support

noncomputable def Q0 : PMF Bool := PMF.pure false

theorem test_not_support_off : ¬ Support P1 Q0 := by
  intro h
  have h1 := h true (by simp [P1])
  simp [Q0] at h1

theorem test_div_off_support_top : renyiDiv P1 Q0 2 = ⊤ :=
  renyiDiv_of_not_support test_not_support_off

theorem test_div_off_support_ne_zero : renyiDiv P1 Q0 2 ≠ 0 := by
  simp [test_div_off_support_top]

theorem test_P1_ne_Q1 : P1 ≠ Q1 := by
  intro h
  have hP : (P1 true).toReal = 1 := by simp [P1]
  have hQ := test_uniform_toReal true
  rw [h] at hP
  rw [hQ] at hP
  norm_num at hP

/-- Regression test: at order 1 the divergence is infinite, not 0. -/
theorem test_div_order_one_top : renyiDiv P1 Q1 1 = ⊤ := by
  unfold renyiDiv
  exact ite_eq_right (fun h => lt_irrefl 1 h.2)

/-- Regression test: below order 1 the divergence is infinite. -/
theorem test_div_order_half_top : renyiDiv P1 Q1 (1/2 : ℝ) = ⊤ :=
  renyiDiv_of_le_one (by norm_num)

theorem test_moment_off_support_top : renyiMoment P1 Q0 2 = ⊤ :=
  renyiMoment_of_not_support test_not_support_off

/-- Regression test: at order 1 the moment is infinite. -/
theorem test_moment_order_one_top : renyiMoment P1 Q1 1 = ⊤ :=
  renyiMoment_of_le_one (by norm_num)

/-- Regression test: below order 1 the moment is infinite. -/
theorem test_moment_order_half_top : renyiMoment P1 Q1 (1/2 : ℝ) = ⊤ :=
  renyiMoment_of_le_one (by norm_num)

theorem test_moment_prod :
    renyiMoment (InformationTheory.prodJoint P1 P1)
      (InformationTheory.prodJoint Q1 Q1) 2 = 4 := by
  rw [renyiMoment_prodJoint, test_moment_pure_uniform,
    show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
    show (4 : EReal) = ((4 : ℝ) : EReal) from rfl,
    ← EReal.coe_mul, EReal.coe_eq_coe_iff]
  norm_num

theorem test_rdpEps2 :
    rdpEps2 (Real.log 2) (1 / 2) 2 = 2 * Real.log 2 := by
  unfold rdpEps2
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num,
    show ((2 : ℝ) - 1) = 1 by norm_num, div_one]
  ring

noncomputable def Mtest : Bool → PMF Bool := fun d => if d then P1 else Q1

def adjTest : Bool → Bool → Prop :=
  fun d d' => d = d' ∨ (d = true ∧ d' = false)

theorem test_isRDP : IsRDP Mtest adjTest 2 (Real.log 2) := by
  refine ⟨Real.log_nonneg (by norm_num), by norm_num, fun d d' hadj => ?_⟩
  simp only [adjTest] at hadj
  rcases hadj with rfl | ⟨rfl, rfl⟩
  · refine ⟨fun w h => h, ?_⟩
    rw [renyiDiv_self _ (by norm_num : (1 : ℝ) < 2)]
    exact_mod_cast Real.log_nonneg (by norm_num)
  · show Support P1 Q1 ∧ renyiDiv P1 Q1 2 ≤ (Real.log 2 : EReal)
    exact ⟨test_support, test_div_pure_uniform.le⟩

theorem test_isRDP_excludes_one (ε : ℝ) : ¬ IsRDP Mtest adjTest 1 ε := by
  intro h
  have h1 := h.2.1
  norm_num at h1

theorem test_isApproxDP :
    CSLibExt.Privacy.DifferentialPrivacy.IsApproxDP Mtest adjTest
      (rdpEps2 (Real.log 2) (1 / 2) 2) (1 / 2) :=
  isApproxDP_of_isRDP (by norm_num) (by norm_num) test_isRDP

theorem test_isRDP_bind :
    IsRDP (fun d => (Mtest d).bind PMF.pure) adjTest 2 (Real.log 2) :=
  isRDP_bind test_isRDP PMF.pure

theorem test_bind_const : Q1.bind (fun _ => Q1) = Q1 := by
  ext y
  simp only [PMF.bind_apply]
  rw [show (∑' x, Q1 x * Q1 y) = (∑' x, Q1 y * Q1 x) from
    tsum_congr (fun x => mul_comm _ _)]
  rw [ENNReal.tsum_mul_left, Q1.tsum_coe, mul_one]

theorem test_moment_bind_le :
    renyiMoment Q1 Q1 2 ≤ renyiMoment P1 Q1 2 := by
  have hPbind : P1.bind (fun _ => Q1) = Q1 := by simp [P1]
  have h := renyiMoment_bind_le (α := 2) P1 Q1 (fun _ => Q1) (by norm_num)
    test_support
  rw [hPbind, test_bind_const] at h
  exact h

#print axioms renyiMoment_bind_le
#print axioms renyiDiv_prodJoint
#print axioms isApproxDP_of_isRDP
#print axioms approx_event_of_renyi

noncomputable def stage2 : Bool → Bool → PMF Bool :=
  fun d y => if y then Mtest d else (Mtest d).bind (fun _ => Q0)

theorem stage2_true (d : Bool) : stage2 d true = Mtest d := by simp [stage2]

theorem stage2_false (d : Bool) :
    stage2 d false = (Mtest d).bind (fun _ => Q0) := by simp [stage2]

theorem test_stage2_isRDP (y : Bool) :
    IsRDP (fun d => stage2 d y) adjTest 2 (Real.log 2) := by
  cases y
  · simp_rw [stage2_false]
    exact isRDP_bind test_isRDP (fun _ => Q0)
  · simp_rw [stage2_true]
    exact test_isRDP

theorem test_isRDP_bind_adaptive :
    IsRDP (fun d => (Mtest d).bind (fun y => (stage2 d y).map (fun z => (y, z))))
      adjTest 2 (Real.log 2 + Real.log 2) :=
  isRDP_bind_adaptive test_isRDP (Real.log_nonneg (by norm_num)) test_stage2_isRDP

#print axioms isRDP_bind_adaptive
#print axioms test_isRDP_bind_adaptive

end CSLibExtTest.Privacy.RenyiDifferentialPrivacyTests
