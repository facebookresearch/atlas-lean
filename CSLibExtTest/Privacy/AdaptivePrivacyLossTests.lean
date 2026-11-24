/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.AdaptivePrivacyLoss
public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Tactic.FinCases
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

/- Part B tests: finite-sum MGF value on the fixture.

Stage masses, losses and drifts are computed by finite case analysis over
explicit transcripts; the MGF sum at `λ = 1` is then exactly `49 / 27`. -/

/-- Stage outputs as explicit pairs. -/
def testFunEquiv : Bool × Bool ≃ (Fin 2 → Bool) :=
  { toFun := fun p i => if i = 0 then p.1 else p.2
    invFun := fun f => (f 0, f 1)
    left_inv := fun p => by
      obtain ⟨b0, b1⟩ := p
      cases b0 <;> cases b1 <;> decide
    right_inv := fun f => by
      funext i
      fin_cases i
      · show (if (0 : Fin 2) = 0 then f 0 else f 1) = f 0
        exact ite_eq_left rfl
      · show (if (1 : Fin 2) = 0 then f 0 else f 1) = f 1
        exact ite_eq_right (by decide) }

/-- Stage-0 mass on a target hit. -/
theorem testK0f_mass_hit (h : Hist Bool Bool 0) (y : Bool)
    (hy : y = xor false h.1) :
    (testK 0 h false y).toReal = 3 / 4 := by
  rw [testK_zero, rrPMF_toReal, ite_eq_left hy]

/-- Stage-0 mass on a target miss. -/
theorem testK0f_mass_miss (h : Hist Bool Bool 0) (y : Bool)
    (hy : y ≠ xor false h.1) :
    (testK 0 h false y).toReal = 1 / 4 := by
  rw [testK_zero, rrPMF_toReal, ite_eq_right hy]

/-- Stage-1 mass on a target hit. -/
theorem testK1f_mass_hit (h : Hist Bool Bool 1) (y : Bool)
    (hy : y = xor (xor false h.1) (h.2 0)) :
    (testK 1 h false y).toReal = 3 / 4 := by
  rw [testK_one, rrPMF_toReal, ite_eq_left hy]

/-- Stage-1 mass on a target miss. -/
theorem testK1f_mass_miss (h : Hist Bool Bool 1) (y : Bool)
    (hy : y ≠ xor (xor false h.1) (h.2 0)) :
    (testK 1 h false y).toReal = 1 / 4 := by
  rw [testK_one, rrPMF_toReal, ite_eq_right hy]

/-- Stage-0 loss on a target hit. -/
theorem testK0_loss_hit (h : Hist Bool Bool 0) (y : Bool)
    (hy : y = xor false h.1) :
    privacyLoss (testK 0 h false) (testK 0 h true) y = Real.log 3 := by
  have hne : y ≠ xor true h.1 := by
    rw [hy]
    cases hc : h.1 <;> decide
  simp only [privacyLoss, testK_zero, rrPMF_toReal, ite_eq_left hy, ite_eq_right hne]
  norm_num

/-- Stage-0 loss on a target miss. -/
theorem testK0_loss_miss (h : Hist Bool Bool 0) (y : Bool)
    (hy : y ≠ xor false h.1) :
    privacyLoss (testK 0 h false) (testK 0 h true) y = -Real.log 3 := by
  have hy' : y = xor true h.1 := by
    cases y <;> cases hc : h.1 <;> simp only [hc] at hy <;> revert hy <;>
      decide
  simp only [privacyLoss, testK_zero, rrPMF_toReal, ite_eq_right hy, ite_eq_left hy']
  rw [show ((1/4:ℝ)/(3/4)) = 1/3 from by norm_num, one_div, Real.log_inv]

/-- Stage-1 loss on a target hit. -/
theorem testK1_loss_hit (h : Hist Bool Bool 1) (y : Bool)
    (hy : y = xor (xor false h.1) (h.2 0)) :
    privacyLoss (testK 1 h false) (testK 1 h true) y = Real.log 3 := by
  have hne : y ≠ xor (xor true h.1) (h.2 0) := by
    rw [hy]
    cases hc : h.1 <;> cases h1 : h.2 0 <;> decide
  simp only [privacyLoss, testK_one, rrPMF_toReal, ite_eq_left hy, ite_eq_right hne]
  norm_num

/-- Stage-1 loss on a target miss. -/
theorem testK1_loss_miss (h : Hist Bool Bool 1) (y : Bool)
    (hy : y ≠ xor (xor false h.1) (h.2 0)) :
    privacyLoss (testK 1 h false) (testK 1 h true) y = -Real.log 3 := by
  have hy' : y = xor (xor true h.1) (h.2 0) := by
    cases y <;> cases hc : h.1 <;> cases h1 : h.2 0 <;>
      simp only [hc, h1] at hy <;> revert hy <;> decide
  simp only [privacyLoss, testK_one, rrPMF_toReal, ite_eq_right hy, ite_eq_left hy']
  rw [show ((1/4:ℝ)/(3/4)) = 1/3 from by norm_num, one_div, Real.log_inv]

/-- Stage drift on the fixture equals half the privacy budget. -/
theorem test_drift (i : ℕ) (h : Hist Bool Bool i) :
    stageDrift testK i h false true = Real.log 3 / 2 := by
  cases i with
  | zero =>
    simp only [stageDrift, Fintype.sum_bool, testK_zero]
    cases hc : h.1 <;>
      simp [rrPMF_toReal, privacyLoss] <;>
      rw [show ((4⁻¹:ℝ)/(3/4)) = 1/3 from by norm_num, one_div,
        Real.log_inv] <;>
      ring
  | succ m =>
    cases m with
    | zero =>
      show stageDrift testK 1 h false true = Real.log 3 / 2
      simp only [stageDrift, Fintype.sum_bool, testK_one]
      cases hc : h.1 <;> cases h1 : h.2 0 <;>
        simp [rrPMF_toReal, privacyLoss] <;>
        rw [show ((4⁻¹:ℝ)/(3/4)) = 1/3 from by norm_num, one_div,
          Real.log_inv] <;>
        ring
    | succ k =>
      simp only [stageDrift, Fintype.sum_bool, testK_succ_succ]
      cases hc : h.1 <;>
        simp [rrPMF_toReal, privacyLoss] <;>
        rw [show ((4⁻¹:ℝ)/(3/4)) = 1/3 from by norm_num, one_div,
          Real.log_inv] <;>
        ring

/-- Exponential evaluations at log-scale centered sums. -/
theorem test_exp_log3 : Real.exp (Real.log 3) = 3 :=
  Real.exp_log (by norm_num)

theorem test_exp_neg_log3 : Real.exp (-Real.log 3) = 1 / 3 := by
  rw [Real.exp_neg, test_exp_log3]
  norm_num

theorem test_exp_neg3_log3 : Real.exp (-3 * Real.log 3) = 1 / 27 := by
  have harg : (-3:ℝ) * Real.log 3
      = -(Real.log 3 + Real.log 3 + Real.log 3) := by ring
  rw [harg, Real.exp_neg, Real.exp_add, Real.exp_add, test_exp_log3]
  norm_num

/-- Transcript mass: both stages hit. -/
theorem test_mass_FFF :
    (transcript testCoin testK 2 false
      (false, ⇑testFunEquiv (false, false))).toReal = 9 / 32 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (false, false))
      = xor false (histPrefix 0 (false, ⇑testFunEquiv (false, false))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (false, false))
      = xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (false, false))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (false, false))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (false, false))) false
      (histOut 0 (false, ⇑testFunEquiv (false, false)))).toReal = 3 / 4 :=
    testK0f_mass_hit _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (false, false))) false
      (histOut 1 (false, ⇑testFunEquiv (false, false)))).toReal = 3 / 4 :=
    testK1f_mass_hit _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (false, ⇑testFunEquiv (false, false))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: both stages hit. -/
theorem test_centered_FFF :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (false, ⇑testFunEquiv (false, false))
      - stageDrift testK i.val
        (histPrefix i (false, ⇑testFunEquiv (false, false))) false true))
    = Real.log 3 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (false, false))
      = xor false (histPrefix 0 (false, ⇑testFunEquiv (false, false))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (false, false))
      = xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (false, false))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (false, false))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (false, ⇑testFunEquiv (false, false)) = Real.log 3 :=
    testK0_loss_hit _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (false, ⇑testFunEquiv (false, false)) = Real.log 3 :=
    testK1_loss_hit _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (false, false))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (false, false))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: both stages miss. -/
theorem test_mass_FTF :
    (transcript testCoin testK 2 false
      (false, ⇑testFunEquiv (true, false))).toReal = 1 / 32 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (true, false))
      ≠ xor false (histPrefix 0 (false, ⇑testFunEquiv (true, false))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (true, false))
      ≠ xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (true, false))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (true, false))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (true, false))) false
      (histOut 0 (false, ⇑testFunEquiv (true, false)))).toReal = 1 / 4 :=
    testK0f_mass_miss _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (true, false))) false
      (histOut 1 (false, ⇑testFunEquiv (true, false)))).toReal = 1 / 4 :=
    testK1f_mass_miss _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (false, ⇑testFunEquiv (true, false))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: both stages miss. -/
theorem test_centered_FTF :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (false, ⇑testFunEquiv (true, false))
      - stageDrift testK i.val
        (histPrefix i (false, ⇑testFunEquiv (true, false))) false true))
    = -3 * Real.log 3 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (true, false))
      ≠ xor false (histPrefix 0 (false, ⇑testFunEquiv (true, false))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (true, false))
      ≠ xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (true, false))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (true, false))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (false, ⇑testFunEquiv (true, false)) = -Real.log 3 :=
    testK0_loss_miss _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (false, ⇑testFunEquiv (true, false)) = -Real.log 3 :=
    testK1_loss_miss _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (true, false))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (true, false))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: stage 0 hits, stage 1 misses. -/
theorem test_mass_FFT :
    (transcript testCoin testK 2 false
      (false, ⇑testFunEquiv (false, true))).toReal = 3 / 32 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (false, true))
      = xor false (histPrefix 0 (false, ⇑testFunEquiv (false, true))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (false, true))
      ≠ xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (false, true))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (false, true))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (false, true))) false
      (histOut 0 (false, ⇑testFunEquiv (false, true)))).toReal = 3 / 4 :=
    testK0f_mass_hit _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (false, true))) false
      (histOut 1 (false, ⇑testFunEquiv (false, true)))).toReal = 1 / 4 :=
    testK1f_mass_miss _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (false, ⇑testFunEquiv (false, true))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: stage 0 hits, stage 1 misses. -/
theorem test_centered_FFT :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (false, ⇑testFunEquiv (false, true))
      - stageDrift testK i.val
        (histPrefix i (false, ⇑testFunEquiv (false, true))) false true))
    = -Real.log 3 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (false, true))
      = xor false (histPrefix 0 (false, ⇑testFunEquiv (false, true))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (false, true))
      ≠ xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (false, true))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (false, true))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (false, ⇑testFunEquiv (false, true)) = Real.log 3 :=
    testK0_loss_hit _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (false, ⇑testFunEquiv (false, true)) = -Real.log 3 :=
    testK1_loss_miss _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (false, true))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (false, true))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: stage 0 misses, stage 1 hits. -/
theorem test_mass_FTT :
    (transcript testCoin testK 2 false
      (false, ⇑testFunEquiv (true, true))).toReal = 3 / 32 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (true, true))
      ≠ xor false (histPrefix 0 (false, ⇑testFunEquiv (true, true))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (true, true))
      = xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (true, true))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (true, true))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (true, true))) false
      (histOut 0 (false, ⇑testFunEquiv (true, true)))).toReal = 1 / 4 :=
    testK0f_mass_miss _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (true, true))) false
      (histOut 1 (false, ⇑testFunEquiv (true, true)))).toReal = 3 / 4 :=
    testK1f_mass_hit _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (false, ⇑testFunEquiv (true, true))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: stage 0 misses, stage 1 hits. -/
theorem test_centered_FTT :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (false, ⇑testFunEquiv (true, true))
      - stageDrift testK i.val
        (histPrefix i (false, ⇑testFunEquiv (true, true))) false true))
    = -Real.log 3 := by
  have hm0 : histOut 0 (false, ⇑testFunEquiv (true, true))
      ≠ xor false (histPrefix 0 (false, ⇑testFunEquiv (true, true))).1 := by
    decide
  have hm1 : histOut 1 (false, ⇑testFunEquiv (true, true))
      = xor (xor false
        (histPrefix 1 (false, ⇑testFunEquiv (true, true))).1)
        ((histPrefix 1 (false, ⇑testFunEquiv (true, true))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (false, ⇑testFunEquiv (true, true)) = -Real.log 3 :=
    testK0_loss_miss _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (false, ⇑testFunEquiv (true, true)) = Real.log 3 :=
    testK1_loss_hit _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (false, ⇑testFunEquiv (true, true))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (false, ⇑testFunEquiv (true, true))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: both stages miss. -/
theorem test_mass_TFF :
    (transcript testCoin testK 2 false
      (true, ⇑testFunEquiv (false, false))).toReal = 1 / 32 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (false, false))
      ≠ xor false (histPrefix 0 (true, ⇑testFunEquiv (false, false))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (false, false))
      ≠ xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (false, false))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (false, false))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (false, false))) false
      (histOut 0 (true, ⇑testFunEquiv (false, false)))).toReal = 1 / 4 :=
    testK0f_mass_miss _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (false, false))) false
      (histOut 1 (true, ⇑testFunEquiv (false, false)))).toReal = 1 / 4 :=
    testK1f_mass_miss _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (true, ⇑testFunEquiv (false, false))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: both stages miss. -/
theorem test_centered_TFF :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (true, ⇑testFunEquiv (false, false))
      - stageDrift testK i.val
        (histPrefix i (true, ⇑testFunEquiv (false, false))) false true))
    = -3 * Real.log 3 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (false, false))
      ≠ xor false (histPrefix 0 (true, ⇑testFunEquiv (false, false))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (false, false))
      ≠ xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (false, false))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (false, false))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (true, ⇑testFunEquiv (false, false)) = -Real.log 3 :=
    testK0_loss_miss _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (true, ⇑testFunEquiv (false, false)) = -Real.log 3 :=
    testK1_loss_miss _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (false, false))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (false, false))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: stage 0 misses, stage 1 hits. -/
theorem test_mass_TFT :
    (transcript testCoin testK 2 false
      (true, ⇑testFunEquiv (false, true))).toReal = 3 / 32 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (false, true))
      ≠ xor false (histPrefix 0 (true, ⇑testFunEquiv (false, true))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (false, true))
      = xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (false, true))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (false, true))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (false, true))) false
      (histOut 0 (true, ⇑testFunEquiv (false, true)))).toReal = 1 / 4 :=
    testK0f_mass_miss _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (false, true))) false
      (histOut 1 (true, ⇑testFunEquiv (false, true)))).toReal = 3 / 4 :=
    testK1f_mass_hit _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (true, ⇑testFunEquiv (false, true))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: stage 0 misses, stage 1 hits. -/
theorem test_centered_TFT :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (true, ⇑testFunEquiv (false, true))
      - stageDrift testK i.val
        (histPrefix i (true, ⇑testFunEquiv (false, true))) false true))
    = -Real.log 3 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (false, true))
      ≠ xor false (histPrefix 0 (true, ⇑testFunEquiv (false, true))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (false, true))
      = xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (false, true))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (false, true))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (true, ⇑testFunEquiv (false, true)) = -Real.log 3 :=
    testK0_loss_miss _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (true, ⇑testFunEquiv (false, true)) = Real.log 3 :=
    testK1_loss_hit _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (false, true))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (false, true))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: both stages hit. -/
theorem test_mass_TTF :
    (transcript testCoin testK 2 false
      (true, ⇑testFunEquiv (true, false))).toReal = 9 / 32 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (true, false))
      = xor false (histPrefix 0 (true, ⇑testFunEquiv (true, false))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (true, false))
      = xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (true, false))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (true, false))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (true, false))) false
      (histOut 0 (true, ⇑testFunEquiv (true, false)))).toReal = 3 / 4 :=
    testK0f_mass_hit _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (true, false))) false
      (histOut 1 (true, ⇑testFunEquiv (true, false)))).toReal = 3 / 4 :=
    testK1f_mass_hit _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (true, ⇑testFunEquiv (true, false))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: both stages hit. -/
theorem test_centered_TTF :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (true, ⇑testFunEquiv (true, false))
      - stageDrift testK i.val
        (histPrefix i (true, ⇑testFunEquiv (true, false))) false true))
    = Real.log 3 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (true, false))
      = xor false (histPrefix 0 (true, ⇑testFunEquiv (true, false))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (true, false))
      = xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (true, false))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (true, false))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (true, ⇑testFunEquiv (true, false)) = Real.log 3 :=
    testK0_loss_hit _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (true, ⇑testFunEquiv (true, false)) = Real.log 3 :=
    testK1_loss_hit _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (true, false))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (true, false))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- Transcript mass: stage 0 hits, stage 1 misses. -/
theorem test_mass_TTT :
    (transcript testCoin testK 2 false
      (true, ⇑testFunEquiv (true, true))).toReal = 3 / 32 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (true, true))
      = xor false (histPrefix 0 (true, ⇑testFunEquiv (true, true))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (true, true))
      ≠ xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (true, true))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (true, true))).2 (0 : Fin 1)) := by
    decide
  have hsm0 : (testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (true, true))) false
      (histOut 0 (true, ⇑testFunEquiv (true, true)))).toReal = 3 / 4 :=
    testK0f_mass_hit _ _ hm0
  have hsm1 : (testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (true, true))) false
      (histOut 1 (true, ⇑testFunEquiv (true, true)))).toReal = 1 / 4 :=
    testK1f_mass_miss _ _ hm1
  have hfact := transcript_toReal_factor testCoin testK 2 false
    (true, ⇑testFunEquiv (true, true))
  rw [hfact]
  simp only [Fin.prod_univ_two]
  rw [testCoin_toReal, hsm0, hsm1]
  norm_num

/-- Centered sum: stage 0 hits, stage 1 misses. -/
theorem test_centered_TTT :
    (∑ i : Fin 2, (stageLoss testK 2 false true i
        (true, ⇑testFunEquiv (true, true))
      - stageDrift testK i.val
        (histPrefix i (true, ⇑testFunEquiv (true, true))) false true))
    = -Real.log 3 := by
  have hm0 : histOut 0 (true, ⇑testFunEquiv (true, true))
      = xor false (histPrefix 0 (true, ⇑testFunEquiv (true, true))).1 := by
    decide
  have hm1 : histOut 1 (true, ⇑testFunEquiv (true, true))
      ≠ xor (xor false
        (histPrefix 1 (true, ⇑testFunEquiv (true, true))).1)
        ((histPrefix 1 (true, ⇑testFunEquiv (true, true))).2 (0 : Fin 1)) := by
    decide
  have hl0 : stageLoss testK 2 false true 0
      (true, ⇑testFunEquiv (true, true)) = Real.log 3 :=
    testK0_loss_hit _ _ hm0
  have hl1 : stageLoss testK 2 false true 1
      (true, ⇑testFunEquiv (true, true)) = -Real.log 3 :=
    testK1_loss_miss _ _ hm1
  have hdr0 : stageDrift testK (0 : Fin 2).val
      (histPrefix 0 (true, ⇑testFunEquiv (true, true))) false true
      = Real.log 3 / 2 :=
    test_drift 0 _
  have hdr1 : stageDrift testK (1 : Fin 2).val
      (histPrefix 1 (true, ⇑testFunEquiv (true, true))) false true
      = Real.log 3 / 2 :=
    test_drift 1 _
  simp only [Fin.sum_univ_two]
  rw [hl0, hl1, hdr0, hdr1]
  ring

/-- MGF sum at `λ = 1`: exact value `49 / 27`. -/
theorem test_mgf_exact :
    (∑ ω : Hist Bool Bool 2, (transcript testCoin testK 2 false ω).toReal
      * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i ω
        - stageDrift testK i.val (histPrefix i ω) false true))) = 49 / 27 := by
  have hprod : (∑ ω : Hist Bool Bool 2,
        (transcript testCoin testK 2 false ω).toReal
        * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i ω
          - stageDrift testK i.val (histPrefix i ω) false true)))
      = ∑ c : Bool, ∑ f : Fin 2 → Bool,
        (transcript testCoin testK 2 false (c, f)).toReal
        * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i (c, f)
          - stageDrift testK i.val (histPrefix i (c, f)) false true)) :=
    Fintype.sum_prod_type _
  have hexp : ∀ c : Bool, (∑ f : Fin 2 → Bool,
        (transcript testCoin testK 2 false (c, f)).toReal
        * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i (c, f)
          - stageDrift testK i.val (histPrefix i (c, f)) false true)))
      = ∑ p : Bool × Bool,
        (transcript testCoin testK 2 false (c, ⇑testFunEquiv p)).toReal
        * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i
          (c, ⇑testFunEquiv p)
          - stageDrift testK i.val (histPrefix i (c, ⇑testFunEquiv p))
            false true)) :=
    fun c => (Equiv.sum_comp testFunEquiv (fun f =>
      (transcript testCoin testK 2 false (c, f)).toReal
      * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i (c, f)
        - stageDrift testK i.val (histPrefix i (c, f)) false true)))).symm
  rw [hprod]
  simp only [hexp, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [test_mass_FFF, test_mass_FFT, test_mass_FTF, test_mass_FTT,
    test_mass_TFF, test_mass_TFT, test_mass_TTF, test_mass_TTT]
  rw [test_centered_FFF, test_centered_FFT, test_centered_FTF,
    test_centered_FTT, test_centered_TFF, test_centered_TFT,
    test_centered_TTF, test_centered_TTT]
  simp only [one_mul]
  rw [test_exp_log3, test_exp_neg_log3, test_exp_neg3_log3]
  norm_num

/-- The MGF value is below the sub-Gaussian bound. -/
theorem test_mgf_bound : (49 / 27 : ℝ) ≤ Real.exp ((Real.log 3) ^ 2) := by
  have h49 : ((49 / 27 : ℝ)) ≤ 2 := by norm_num
  have h2 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    norm_num at h
    exact h
  have hlog1 : (1:ℝ) ≤ Real.log 3 := by
    have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hlog : Real.log (Real.exp 1) ≤ Real.log 3 :=
      Real.log_le_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at hlog
  have hsq : (1:ℝ) ≤ (Real.log 3) ^ 2 := by
    have h0 : (0:ℝ) ≤ Real.log 3 := le_trans zero_le_one hlog1
    have hmul := mul_le_mul hlog1 hlog1 zero_le_one h0
    simp only [mul_one] at hmul
    rw [← pow_two] at hmul
    exact hmul
  have h3 : Real.exp 1 ≤ Real.exp ((Real.log 3) ^ 2) :=
    Real.exp_le_exp.mpr hsq
  exact h49.trans (h2.trans h3)

/-- The MGF bound applies to the fixture. -/
theorem test_mgf_prod_applies :
    (∑ ω : Hist Bool Bool 2, (transcript testCoin testK 2 false ω).toReal
      * Real.exp (1 * ∑ i : Fin 2, (stageLoss testK 2 false true i ω
        - stageDrift testK i.val (histPrefix i ω) false true)))
    ≤ Real.exp ((((2:ℕ)):ℝ) * (1:ℝ) ^ 2 * (Real.log 3) ^ 2 / 2) :=
  transcript_centered_mgf_le testCoin testK testAdj (Real.log 3) 2 false true 1
    testK_isDP (Real.log_nonneg (by norm_num)) trivial trivial

/- The tail bounds are not instantiated on this fixture: at `k = 2`,
`ε = log 3` the `k * (ε * (exp ε - 1)) + t` threshold sits strictly above
the maximum transcript loss `2 * log 3`, so the event is empty and any
such test would be vacuous. The exact MGF value above carries nonvacuity. -/

#print axioms transcript_centered_mgf_le
#print axioms transcript_tail_le
#print axioms transcript_tail_outer_le

/- Part C tests: pure-stage advanced composition.

The corollary is instantiated on the randomized-response fixture
(`ε = log 3`) at `δ' = 1 / 2`: two stages, one stage, and zero stages,
plus a positive-length zero-budget case with a database-independent
kernel. -/

/-- Database-independent test kernel (constant coin). -/
noncomputable def testK0 : (n : ℕ) → Hist Bool Bool n → Bool → PMF Bool :=
  fun _ _ _ => testCoin

theorem testK0_isDP (n : ℕ) (h : Hist Bool Bool n) :
    IsDP (fun d => testK0 n h d) testAdj 0 :=
  isDP_const testCoin testAdj

/-- Advanced composition on the two-stage fixture. -/
theorem test_advcomp_two_stage :
    IsApproxDP (fun d => transcript testCoin testK 2 d) testAdj
      (Real.log 3 * Real.sqrt (2 * ((2 : ℕ) : ℝ) * Real.log (1 / (1 / 2 : ℝ))) +
        ((2 : ℕ) : ℝ) * (Real.log 3 * (Real.exp (Real.log 3) - 1)))
      (1 / 2 : ℝ) :=
  transcript_isApproxDP_advanced_composition_pure testCoin testK testAdj
    (Real.log 3) 2 (1 / 2) testK_isDP (Real.log_nonneg (by norm_num))
    (fun d d' _ => trivial) (by norm_num) (by norm_num)

/-- Advanced composition with a single stage. -/
theorem test_advcomp_one_stage :
    IsApproxDP (fun d => transcript testCoin testK 1 d) testAdj
      (Real.log 3 * Real.sqrt (2 * ((1 : ℕ) : ℝ) * Real.log (1 / (1 / 2 : ℝ))) +
        ((1 : ℕ) : ℝ) * (Real.log 3 * (Real.exp (Real.log 3) - 1)))
      (1 / 2 : ℝ) :=
  transcript_isApproxDP_advanced_composition_pure testCoin testK testAdj
    (Real.log 3) 1 (1 / 2) testK_isDP (Real.log_nonneg (by norm_num))
    (fun d d' _ => trivial) (by norm_num) (by norm_num)

/-- Advanced composition with zero stages. -/
theorem test_advcomp_zero_stage :
    IsApproxDP (fun d => transcript testCoin testK 0 d) testAdj
      (Real.log 3 * Real.sqrt (2 * ((0 : ℕ) : ℝ) * Real.log (1 / (1 / 2 : ℝ))) +
        ((0 : ℕ) : ℝ) * (Real.log 3 * (Real.exp (Real.log 3) - 1)))
      (1 / 2 : ℝ) :=
  transcript_isApproxDP_advanced_composition_pure testCoin testK testAdj
    (Real.log 3) 0 (1 / 2) testK_isDP (Real.log_nonneg (by norm_num))
    (fun d d' _ => trivial) (by norm_num) (by norm_num)

/-- Advanced composition at zero budget with a database-independent kernel. -/
theorem test_advcomp_zero_budget :
    IsApproxDP (fun d => transcript testCoin testK0 2 d) testAdj
      (0 * Real.sqrt (2 * ((2 : ℕ) : ℝ) * Real.log (1 / (1 / 2 : ℝ))) +
        ((2 : ℕ) : ℝ) * (0 * (Real.exp 0 - 1)))
      (1 / 2 : ℝ) :=
  transcript_isApproxDP_advanced_composition_pure testCoin testK0 testAdj
    0 2 (1 / 2) testK0_isDP le_rfl
    (fun d d' _ => trivial) (by norm_num) (by norm_num)

#print axioms transcript_isApproxDP_of_tail
#print axioms transcript_isApproxDP_advanced_composition_pure

/- Domination-transport tests.

With `m = 1` and equal kernels the bound is reflexive; with `m = 1 / 2` a
constant randomized-response kernel is dominated by the fair coin, checked
by finite computation both at each stage and at the named transcript. -/

/-- Domination with `m = 1` and equal kernels, at `testOmega`. -/
theorem test_domination_one_refl :
    (1 : ℝ) ^ 2 * (transcript testCoin testK 2 false testOmega).toReal
      ≤ (transcript testCoin testK 2 false testOmega).toReal := by
  have h := transcript_domination testCoin testK testK false false 2 1
    zero_le_one le_rfl (fun n _ h y => le_of_eq (one_mul _))
  exact h testOmega

/-- Constant dominated kernel for the `m = 1 / 2` test. -/
noncomputable def domL : (n : ℕ) → Hist Bool Bool n → Bool → PMF Bool :=
  fun _ _ _ => rrPMF false

/-- Constant dominating kernel for the `m = 1 / 2` test. -/
noncomputable def domK : (n : ℕ) → Hist Bool Bool n → Bool → PMF Bool :=
  fun _ _ _ => testCoin

/-- Stage domination at `m = 1 / 2`, by finite case analysis. -/
theorem test_domination_stage_half (i : Fin 2) :
    (1 / 2 : ℝ)
        * (domL i.val (histPrefix i testOmega) false (histOut i testOmega)).toReal
      ≤ (domK i.val (histPrefix i testOmega) false (histOut i testOmega)).toReal := by
  show (1 / 2 : ℝ) * (rrPMF false (histOut i testOmega)).toReal
    ≤ (testCoin (histOut i testOmega)).toReal
  rw [rrPMF_toReal, testCoin_toReal]
  split_ifs <;> norm_num

/-- Transcript domination at `m = 1 / 2`, by explicit computation. -/
theorem test_domination_half_compute :
    (1 / 2 : ℝ) ^ 2 * (transcript testCoin domL 2 false testOmega).toReal
      ≤ (transcript testCoin domK 2 false testOmega).toReal := by
  have hL := transcript_toReal_factor testCoin domL 2 false testOmega
  have hK := transcript_toReal_factor testCoin domK 2 false testOmega
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one] at hL hK
  have eL0 : (domL 0 (histPrefix 0 testOmega) false (histOut 0 testOmega)).toReal
      = 3 / 4 := by
    show (rrPMF false false).toReal = 3 / 4
    rw [rrPMF_toReal, ite_eq_left rfl]
  have eL1 : (domL 1 (histPrefix 1 testOmega) false (histOut 1 testOmega)).toReal
      = 3 / 4 := by
    show (rrPMF false false).toReal = 3 / 4
    rw [rrPMF_toReal, ite_eq_left rfl]
  have eK0 : (domK 0 (histPrefix 0 testOmega) false (histOut 0 testOmega)).toReal
      = 1 / 2 :=
    testCoin_toReal _
  have eK1 : (domK 1 (histPrefix 1 testOmega) false (histOut 1 testOmega)).toReal
      = 1 / 2 :=
    testCoin_toReal _
  rw [hL, hK, testCoin_toReal, eL0, eL1, eK0, eK1]
  norm_num

/-- Transcript domination at `m = 1 / 2`, via `transcript_domination`. -/
theorem test_domination_half_via :
    (1 / 2 : ℝ) ^ 2 * (transcript testCoin domL 2 false testOmega).toReal
      ≤ (transcript testCoin domK 2 false testOmega).toReal := by
  have h := transcript_domination testCoin domK domL false false 2 (1 / 2)
    (by norm_num) (by norm_num) (fun n _ h y => by
      show (1 / 2 : ℝ) * (rrPMF false y).toReal ≤ (testCoin y).toReal
      rw [rrPMF_toReal, testCoin_toReal]
      split_ifs <;> norm_num)
  exact h testOmega

#print axioms transcript_domination
#print axioms test_domination_one_refl
#print axioms test_domination_stage_half
#print axioms test_domination_half_compute
#print axioms test_domination_half_via


-- Pair-local assembly tests: two-sided `maxDivLE` for the test kernels at
-- `ε = log 3`, the `k = 2`, `δ' = 1 / 2` advanced-composition instance for the
-- fixture, and the `ε = 0`, `P = Q` adapter sanity check.

-- Convert an `IsDP`-shaped `ENNReal` bound into a real-mass bound.
theorem test_pair_toReal_le_of_le {a b : ENNReal} {c : ℝ} (hc : 0 ≤ c)
    (hb : b ≠ ⊤) (h : a ≤ ENNReal.ofReal c * b) :
    a.toReal ≤ c * b.toReal := by
  have hfin : ENNReal.ofReal c * b ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb
  have hle := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hle

-- Two-sided `maxDivLE` for the test kernels at `ε = log 3`, forward direction.
open CSLibExt.Privacy.MaxDivergenceDecomposition in
theorem test_pair_maxDivLE_false_true (n : ℕ) (h : Hist Bool Bool n) :
    maxDivLE (testK n h false) (testK n h true) (Real.log 3) := by
  intro o
  exact test_pair_toReal_le_of_le (Real.exp_pos _).le
    ((testK n h true).apply_ne_top o) ((testK_isDP n h).2 false true trivial o)

-- Two-sided `maxDivLE` for the test kernels at `ε = log 3`, reverse direction.
open CSLibExt.Privacy.MaxDivergenceDecomposition in
theorem test_pair_maxDivLE_true_false (n : ℕ) (h : Hist Bool Bool n) :
    maxDivLE (testK n h true) (testK n h false) (Real.log 3) := by
  intro o
  exact test_pair_toReal_le_of_le (Real.exp_pos _).le
    ((testK n h false).apply_ne_top o) ((testK_isDP n h).2 true false trivial o)

-- Pairwise advanced composition for the two-stage fixture at `δ' = 1 / 2`.
open CSLibExt.Privacy.MaxDivergenceDecomposition in
theorem test_pair_adv_comp_pair :
    approxMaxDivLE (transcript testCoin testK 2 false) (transcript testCoin testK 2 true)
      (Real.log 3 * Real.sqrt (2 * ((2 : ℕ) : ℝ) * Real.log (1 / (1 / 2 : ℝ))) +
        ((2 : ℕ) : ℝ) * (Real.log 3 * (Real.exp (Real.log 3) - 1))) (1 / 2 : ℝ) ∧
    approxMaxDivLE (transcript testCoin testK 2 true) (transcript testCoin testK 2 false)
      (Real.log 3 * Real.sqrt (2 * ((2 : ℕ) : ℝ) * Real.log (1 / (1 / 2 : ℝ))) +
        ((2 : ℕ) : ℝ) * (Real.log 3 * (Real.exp (Real.log 3) - 1))) (1 / 2 : ℝ) :=
  transcript_approxMaxDivLE_advanced_composition_pair testCoin testK (Real.log 3) 2 (1 / 2)
    (Real.log_nonneg (by norm_num))
    (fun n h => ⟨test_pair_maxDivLE_false_true n h, test_pair_maxDivLE_true_false n h⟩)
    (by norm_num) (by norm_num)

-- Adapter sanity: `maxDivLE` is reflexive at `ε = 0`.
open CSLibExt.Privacy.MaxDivergenceDecomposition in
theorem test_pair_adapter_zero_refl (P : PMF Bool) : maxDivLE P P 0 := by
  intro o
  rw [Real.exp_zero, one_mul]

#print axioms transcript_approxMaxDivLE_advanced_composition_pair

end CSLibExt.Privacy.DifferentialPrivacy
