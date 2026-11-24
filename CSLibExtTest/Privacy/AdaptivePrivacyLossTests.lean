/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.AdaptivePrivacyLoss
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Tests for the adaptive transcript model

Two-stage randomized response over `Bool` databases with fair public coins.
Stage targets genuinely depend on history: stage 0 aims at `d XOR c` and
stage 1 at `d XOR c XOR y₀`. Checks cover transcript normalization, stage
`IsDP` facts at `ε = log 3`, and the loss decomposition at the all-false
transcript (`log 9 = log 3 + log 3`).
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- Test adjacency: every pair of databases is adjacent. -/
def testAdj : Bool → Bool → Prop := fun _ _ => True

/-- Fair public coin. -/
noncomputable def testCoin : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2 : ℝ)) (by
    simp only [Fintype.sum_bool]
    have h1 : (0:ℝ) ≤ 1 / 2 := by norm_num
    rw [← ENNReal.ofReal_add h1 h1]
    have h12 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    rw [h12, ENNReal.ofReal_one])

/-- Randomized response toward `t` with success probability `3 / 4`. -/
noncomputable def rrPMF (t : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y => ENNReal.ofReal (if y = t then (3 / 4 : ℝ) else (1 / 4 : ℝ))) (by
    cases t with
    | true =>
      simp only [Fintype.sum_bool, ite_eq_left True.intro,
        ite_eq_right (by decide : ¬ (false : Bool) = true)]
      have h34 : (0:ℝ) ≤ 3 / 4 := by norm_num
      have h14 : (0:ℝ) ≤ 1 / 4 := by norm_num
      rw [← ENNReal.ofReal_add h34 h14]
      have hadd : (3 / 4 : ℝ) + 1 / 4 = 1 := by norm_num
      rw [hadd, ENNReal.ofReal_one]
    | false =>
      simp only [Fintype.sum_bool, ite_eq_left True.intro,
        ite_eq_right (by decide : ¬ (true : Bool) = false)]
      have h14 : (0:ℝ) ≤ 1 / 4 := by norm_num
      have h34 : (0:ℝ) ≤ 3 / 4 := by norm_num
      rw [← ENNReal.ofReal_add h14 h34]
      have hadd : (1 / 4 : ℝ) + 3 / 4 = 1 := by norm_num
      rw [hadd, ENNReal.ofReal_one])

/-- Real masses of randomized response. -/
theorem rrPMF_toReal (t y : Bool) :
    (rrPMF t y).toReal = (if y = t then (3 / 4 : ℝ) else (1 / 4 : ℝ)) := by
  simp only [rrPMF, PMF.ofFintype_apply]
  have hnn : 0 ≤ (if y = t then (3 / 4 : ℝ) else (1 / 4 : ℝ)) := by
    split_ifs <;> norm_num
  rw [ENNReal.toReal_ofReal hnn]

/-- Randomized-response ratios are bounded by `3` pointwise. -/
theorem rrPMF_le_three (t t' o : Bool) :
    rrPMF t o ≤ ENNReal.ofReal 3 * rrPMF t' o := by
  cases t <;> cases t' <;> cases o <;>
    simp only [rrPMF, PMF.ofFintype_apply, ite_eq_left True.intro,
      ite_eq_right (by decide : ¬ (false : Bool) = true),
      ite_eq_right (by decide : ¬ (true : Bool) = false)] <;>
    rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3 by norm_num)] <;>
    exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Test stage kernels: randomized response with history-dependent targets. -/
noncomputable def testK : (n : ℕ) → Hist Bool Bool n → Bool → PMF Bool
  | 0, h, d => rrPMF (xor d h.1)
  | 1, h, d => rrPMF (xor (xor d h.1) (h.2 0))
  | Nat.succ (Nat.succ _), h, d => rrPMF (xor d h.1)

theorem testK_zero (h : Hist Bool Bool 0) (d : Bool) :
    testK 0 h d = rrPMF (xor d h.1) := rfl

theorem testK_one (h : Hist Bool Bool 1) (d : Bool) :
    testK 1 h d = rrPMF (xor (xor d h.1) (h.2 0)) := rfl

theorem testK_succ_succ (n : ℕ) (h : Hist Bool Bool (Nat.succ (Nat.succ n)))
    (d : Bool) :
    testK (Nat.succ (Nat.succ n)) h d = rrPMF (xor d h.1) := rfl

/-- Test stage kernels are `log 3`-DP at every history. -/
theorem testK_isDP (n : ℕ) (h : Hist Bool Bool n) :
    IsDP (fun d => testK n h d) testAdj (Real.log 3) := by
  have h3 : (0:ℝ) < 3 := by norm_num
  cases n with
  | zero =>
    refine ⟨Real.log_nonneg (by norm_num), fun d d' _ o => ?_⟩
    simp only [testK_zero, Real.exp_log h3]
    exact rrPMF_le_three _ _ _
  | succ m =>
    cases m with
    | zero =>
      show IsDP (fun d => testK 1 h d) testAdj (Real.log 3)
      refine ⟨Real.log_nonneg (by norm_num), fun d d' _ o => ?_⟩
      simp only [testK_one, Real.exp_log h3]
      exact rrPMF_le_three _ _ _
    | succ k =>
      refine ⟨Real.log_nonneg (by norm_num), fun d d' _ o => ?_⟩
      simp only [testK_succ_succ, Real.exp_log h3]
      exact rrPMF_le_three _ _ _

/-- Transcript laws normalize. -/
theorem test_transcript_normalize (d : Bool) :
    ∑ ω : Hist Bool Bool 2, transcript testCoin testK 2 d ω = 1 := by
  have h := (transcript testCoin testK 2 d).tsum_coe
  rw [tsum_fintype] at h
  exact h

/-- The all-false transcript. -/
def testOmega : Hist Bool Bool 2 := (false, fun _ => false)

theorem testCoin_toReal (c : Bool) : (testCoin c).toReal = 1 / 2 := by
  simp only [testCoin, PMF.ofFintype_apply]
  have hnn : (0:ℝ) ≤ 1 / 2 := by norm_num
  rw [ENNReal.toReal_ofReal hnn]

theorem testK0false :
    (testK 0 (histPrefix 0 testOmega) false (histOut 0 testOmega)).toReal
      = 3 / 4 := by
  rw [testK_zero]
  show (rrPMF false false).toReal = 3 / 4
  rw [rrPMF_toReal, ite_eq_left rfl]

theorem testK0true :
    (testK 0 (histPrefix 0 testOmega) true (histOut 0 testOmega)).toReal
      = 1 / 4 := by
  rw [testK_zero]
  show (rrPMF true false).toReal = 1 / 4
  rw [rrPMF_toReal, ite_eq_right (by decide : ¬ (false : Bool) = true)]

theorem testK1false :
    (testK 1 (histPrefix 1 testOmega) false (histOut 1 testOmega)).toReal
      = 3 / 4 := by
  rw [testK_one]
  show (rrPMF false false).toReal = 3 / 4
  rw [rrPMF_toReal, ite_eq_left rfl]

theorem testK1true :
    (testK 1 (histPrefix 1 testOmega) true (histOut 1 testOmega)).toReal
      = 1 / 4 := by
  rw [testK_one]
  show (rrPMF true false).toReal = 1 / 4
  rw [rrPMF_toReal, ite_eq_right (by decide : ¬ (false : Bool) = true)]

theorem test_mass_false :
    (transcript testCoin testK 2 false testOmega).toReal = 9 / 32 := by
  have hfact := transcript_toReal_factor testCoin testK 2 false testOmega
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one] at hfact
  rw [hfact, testCoin_toReal, testK0false, testK1false]
  norm_num

theorem test_mass_true :
    (transcript testCoin testK 2 true testOmega).toReal = 1 / 32 := by
  have hfact := transcript_toReal_factor testCoin testK 2 true testOmega
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one] at hfact
  rw [hfact, testCoin_toReal, testK0true, testK1true]
  norm_num

theorem test_mem :
    testOmega ∈ (transcript testCoin testK 2 false).support := by
  rw [PMF.mem_support_iff]
  intro h0
  have h := test_mass_false
  rw [h0, ENNReal.toReal_zero] at h
  norm_num at h

theorem test_stage0_loss :
    privacyLoss (testK 0 (histPrefix 0 testOmega) false)
      (testK 0 (histPrefix 0 testOmega) true) (histOut 0 testOmega)
      = Real.log 3 := by
  simp only [privacyLoss]
  rw [testK0false, testK0true]
  have h31 : ((3 / 4 : ℝ) / (1 / 4)) = 3 := by norm_num
  rw [h31]

theorem test_stage1_loss :
    privacyLoss (testK 1 (histPrefix 1 testOmega) false)
      (testK 1 (histPrefix 1 testOmega) true) (histOut 1 testOmega)
      = Real.log 3 := by
  simp only [privacyLoss]
  rw [testK1false, testK1true]
  have h31 : ((3 / 4 : ℝ) / (1 / 4)) = 3 := by norm_num
  rw [h31]

/-- Log arithmetic for the all-false transcript values. -/
theorem test_log9 : Real.log 9 = 2 * Real.log 3 := by
  have h9 : (9:ℝ) = 3 ^ 2 := by norm_num
  rw [h9, Real.log_pow]
  norm_num

/-- Loss decomposition at the all-false transcript: `log 9 = log 3 + log 3`. -/
theorem test_decomp_allFalse :
    Real.log 9 = Real.log 3 + Real.log 3 := by
  have hdecomp := transcript_loss_decomp testCoin testK testAdj (Real.log 3) 2
    false true testK_isDP (Real.log_nonneg (by norm_num)) trivial trivial
    testOmega test_mem
  rw [test_mass_false, test_mass_true] at hdecomp
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one] at hdecomp
  rw [test_stage0_loss, test_stage1_loss] at hdecomp
  have h93 : ((9 / 32 : ℝ) / (1 / 32)) = 9 := by norm_num
  rw [h93] at hdecomp
  exact hdecomp

#print axioms transcript_loss_decomp
#print axioms stageDrift_nonneg
#print axioms stageDrift_le

end CSLibExt.Privacy.DifferentialPrivacy
