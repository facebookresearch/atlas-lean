/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Privacy.HypothesisTesting

open CSLibExt.Privacy.HypothesisTesting
open scoped BigOperators
open scoped ENNReal

/-!
# Tests for DP as hypothesis testing

Numeric checks for the `3/4` vs `1/4` boundary pair: atom values, H1 event
bounds in both orders, and tradeoff values at levels `0`, `1/4` (in the main
file) and `1`.
-/

/-! ## Atom values of the boundary pair -/

example : (PH5 true).toReal = 3/4 := PH5_true

example : (PH5 false).toReal = 1/4 := PH5_false

example : (QH5 true).toReal = 1/4 := QH5_true

example : (QH5 false).toReal = 3/4 := QH5_false

/-! ## H1 numeric checks in both directions -/

example : (∑ w ∈ ({false} : Finset Bool), (PH5 w).toReal)
    ≤ Real.exp (Real.log 3) * (∑ w ∈ ({false} : Finset Bool),
      (QH5 w).toReal) + 0 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hexp : Real.exp (Real.log 3) = 3 := Real.exp_log h3
  rw [Finset.sum_singleton (fun w => (PH5 w).toReal) false,
    Finset.sum_singleton (fun w => (QH5 w).toReal) false,
    PH5_false, QH5_false, hexp]
  norm_num

example : (∑ w ∈ ({false} : Finset Bool), (QH5 w).toReal)
    ≤ Real.exp (Real.log 3) * (∑ w ∈ ({false} : Finset Bool),
      (PH5 w).toReal) + 0 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hexp : Real.exp (Real.log 3) = 3 := Real.exp_log h3
  rw [Finset.sum_singleton (fun w => (QH5 w).toReal) false,
    Finset.sum_singleton (fun w => (PH5 w).toReal) false,
    QH5_false, PH5_false, hexp]
  norm_num

example : KOVpair Bool PH5 QH5 (Real.log 3) 0 := kovpair_PH5_QH5

example : KOVpair Bool QH5 PH5 (Real.log 3) 0 :=
  kovpair_symm Bool PH5 QH5 (Real.log 3) 0 kovpair_PH5_QH5

/-! ## The always-accept test has type-II error `1` -/

example : betaOf Bool QH5 (fun _ => (0 : ℝ)) = 1 :=
  betaOf_phi0 Bool QH5

/-! ## Tradeoff at level `0` for the full-support pair -/

/-- At level `0`, the tradeoff of the boundary pair is `1`. This uses full
support of `PH5`: any feasible test must vanish everywhere. The general
claim is false. -/
theorem tradeoff_PH5_QH5_zero : tradeoff Bool PH5 QH5 0 = 1 := by
  apply le_antisymm
  · have htest0 : IsTest Bool (fun _ => (0 : ℝ)) := test_phi0 Bool
    have hα : alphaOf Bool PH5 (fun _ => (0 : ℝ)) ≤ 0 :=
      le_of_eq (alphaOf_phi0 Bool PH5)
    have h := tradeoff_le_betaOf Bool PH5 QH5 0 (fun _ => (0 : ℝ))
      (le_refl 0) htest0 hα
    rw [betaOf_phi0 Bool QH5] at h
    exact h
  · refine le_tradeoff Bool PH5 QH5 0 1 (le_refl 0) ?_
    intro phi hphi hαphi
    have hnn : 0 ≤ alphaOf Bool PH5 phi :=
      alphaOf_nonneg Bool PH5 phi hphi
    have hzero : alphaOf Bool PH5 phi = 0 := le_antisymm hαphi hnn
    have hterm : ∀ w ∈ (Finset.univ : Finset Bool),
        (PH5 w).toReal * phi w = 0 := by
      have hiff : (∑ w, (PH5 w).toReal * phi w) = 0 ↔
          ∀ w ∈ (Finset.univ : Finset Bool), (PH5 w).toReal * phi w = 0 :=
        Finset.sum_eq_zero_iff_of_nonneg (fun w _ =>
          mul_nonneg ENNReal.toReal_nonneg (hphi w).1)
      have hzero' : ∑ w, (PH5 w).toReal * phi w = 0 := hzero
      exact hiff.mp hzero'
    have hphi0 : ∀ w : Bool, phi w = 0 := by
      intro w
      have ht := hterm w (Finset.mem_univ w)
      have hpos := PH5_pos w
      rcases mul_eq_zero.mp ht with hP | hph
      · exact absurd hP (ne_of_gt hpos)
      · exact hph
    have hβ : betaOf Bool QH5 phi = 1 := by
      have hpt : ∀ w : Bool, (QH5 w).toReal * (1 - phi w)
          = (QH5 w).toReal := by
        intro w
        rw [hphi0 w, sub_zero, mul_one]
      simp only [betaOf, hpt]
      exact pmf_toReal_sum Bool QH5
    exact le_of_eq hβ.symm

/-! ## Tradeoff at level `1` is `0`, in general -/

example : tradeoff Bool PH5 QH5 1 = 0 := tradeoff_at_one Bool PH5 QH5

example (Ω : Type*) [Fintype Ω] (P Q : PMF Ω) : tradeoff Ω P Q 1 = 0 :=
  tradeoff_at_one Ω P Q

/-! ## The lower bound at level `0` -/

/-- At level `0` with `eps ≥ 0` and `delta ≤ 1`, the f-DP lower bound is
exactly `1 - delta`. -/
theorem fEpsDelta_zero_eq (eps delta : ℝ) (hε : 0 ≤ eps) (hδ : delta ≤ 1) :
    fEpsDelta eps delta 0 = 1 - delta := by
  have hE' : Real.exp (-eps) ≤ 1 := by
    have hle : Real.exp (-eps) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by linarith : -eps ≤ (0 : ℝ))
    rw [Real.exp_zero] at hle
    exact hle
  have hnn : 0 ≤ 1 - delta := by linarith
  have h2 : Real.exp (-eps) * (1 - delta - 0) ≤ 1 - delta := by
    have hmul := mul_le_mul_of_nonneg_right hE' hnn
    simp only [one_mul] at hmul
    simp only [sub_zero]
    exact hmul
  have hmax1 : max (1 - delta - Real.exp eps * 0)
      (Real.exp (-eps) * (1 - delta - 0)) = 1 - delta := by
    have e1 : (1 - delta - Real.exp eps * 0 : ℝ) = 1 - delta := by
      simp only [mul_zero, sub_zero]
    rw [e1]
    exact max_eq_left h2
  show max 0 (max (1 - delta - Real.exp eps * 0)
    (Real.exp (-eps) * (1 - delta - 0))) = 1 - delta
  rw [hmax1]
  exact max_eq_right hnn

/-! ## Axiom checks -/

#print axioms kovpair_iff_event_bounds
#print axioms kovpair_forward_tradeoff_ge
#print axioms tradeoff_PH5_QH5_quarter
#print axioms tradeoff_at_one
#print axioms isApproxDPFin_iff_isApproxDP
#print axioms isApproxDP_iff_forall_kovpair

/-! ## Four-outcome randomized-response dominance tests -/

theorem test_rrC_delta_one (eps : ℝ) : rrC eps 1 = 0 := by
  unfold rrC
  norm_num

theorem test_rrC_zero_eps (delta : ℝ) : rrC 0 delta = (1 - delta) / 2 := by
  unfold rrC
  rw [Real.exp_zero]
  norm_num

theorem test_rr_exp_log3 : Real.exp (Real.log 3) = 3 :=
  Real.exp_log (by norm_num)

theorem test_rr_exp_neg_log3 : Real.exp (-Real.log 3) = 1/3 := by
  have hEE : Real.exp (-Real.log 3) * Real.exp (Real.log 3) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [test_rr_exp_log3] at hEE
  linarith [hEE]

theorem test_rr_log3_nonneg : (0:ℝ) ≤ Real.log 3 :=
  Real.log_nonneg (by norm_num)

theorem test_rr_max_self (x : ℝ) : max x x = x :=
  le_antisymm (max_le (le_refl x) (le_refl x)) (le_max_left x x)

theorem test_rrC_log3_half : rrC (Real.log 3) (1/2) = 1/8 := by
  unfold rrC
  rw [test_rr_exp_log3]
  norm_num

theorem test_rrMass0_zero : rrMass0 (Real.log 3) (1/2) 0 = 1/2 := by
  simp [rrMass0]

theorem test_rrMass0_one : rrMass0 (Real.log 3) (1/2) 1 = 3/8 := by
  have hval : rrMass0 (Real.log 3) (1/2) 1
      = Real.exp (Real.log 3) * rrC (Real.log 3) (1/2) := by simp [rrMass0]
  rw [hval, test_rr_exp_log3, test_rrC_log3_half]
  norm_num

theorem test_rrMass0_two : rrMass0 (Real.log 3) (1/2) 2 = 1/8 := by
  have hval : rrMass0 (Real.log 3) (1/2) 2 = rrC (Real.log 3) (1/2) := by
    simp [rrMass0]
  rw [hval, test_rrC_log3_half]

theorem test_rrMass0_three : rrMass0 (Real.log 3) (1/2) 3 = 0 := by
  simp [rrMass0]

theorem test_rrMass1_zero : rrMass1 (Real.log 3) (1/2) 0 = 0 := by
  simp [rrMass1]

theorem test_rrMass1_one : rrMass1 (Real.log 3) (1/2) 1 = 1/8 := by
  have hval : rrMass1 (Real.log 3) (1/2) 1 = rrC (Real.log 3) (1/2) := by
    simp [rrMass1]
  rw [hval, test_rrC_log3_half]

theorem test_rrMass1_two : rrMass1 (Real.log 3) (1/2) 2 = 3/8 := by
  have hval : rrMass1 (Real.log 3) (1/2) 2
      = Real.exp (Real.log 3) * rrC (Real.log 3) (1/2) := by simp [rrMass1]
  rw [hval, test_rr_exp_log3, test_rrC_log3_half]
  norm_num

theorem test_rrMass1_three : rrMass1 (Real.log 3) (1/2) 3 = 1/2 := by
  simp [rrMass1]

theorem test_rrR0_toReal_zero (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR0 (Real.log 3) (1/2) hδ0 hδ1) 0).toReal = 1/2 := by
  rw [rrR0_toReal_zero]

theorem test_rrR0_toReal_one (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR0 (Real.log 3) (1/2) hδ0 hδ1) 1).toReal = 3/8 := by
  rw [rrR0_toReal_one, test_rr_exp_log3, test_rrC_log3_half]
  norm_num

theorem test_rrR0_toReal_two (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR0 (Real.log 3) (1/2) hδ0 hδ1) 2).toReal = 1/8 := by
  rw [rrR0_toReal_two, test_rrC_log3_half]

theorem test_rrR0_toReal_three (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR0 (Real.log 3) (1/2) hδ0 hδ1) 3).toReal = 0 := by
  rw [rrR0_toReal_three]

theorem test_rrR1_toReal_zero (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR1 (Real.log 3) (1/2) hδ0 hδ1) 0).toReal = 0 := by
  rw [rrR1_toReal_zero]

theorem test_rrR1_toReal_one (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR1 (Real.log 3) (1/2) hδ0 hδ1) 1).toReal = 1/8 := by
  rw [rrR1_toReal_one, test_rrC_log3_half]

theorem test_rrR1_toReal_two (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR1 (Real.log 3) (1/2) hδ0 hδ1) 2).toReal = 3/8 := by
  rw [rrR1_toReal_two, test_rr_exp_log3, test_rrC_log3_half]
  norm_num

theorem test_rrR1_toReal_three (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    ((rrR1 (Real.log 3) (1/2) hδ0 hδ1) 3).toReal = 1/2 := by
  rw [rrR1_toReal_three]

theorem test_rrMass0_zero_delta_zero (eps : ℝ) : rrMass0 eps 0 0 = 0 := by
  simp [rrMass0]

theorem test_rrMass0_three_delta_zero (eps : ℝ) : rrMass0 eps 0 3 = 0 := by
  simp [rrMass0]

theorem test_rrMass1_zero_delta_zero (eps : ℝ) : rrMass1 eps 0 0 = 0 := by
  simp [rrMass1]

theorem test_rrMass1_three_delta_zero (eps : ℝ) : rrMass1 eps 0 3 = 0 := by
  simp [rrMass1]

theorem test_rrMass0_middle_sum_delta_zero (eps : ℝ) :
    rrMass0 eps 0 1 + rrMass0 eps 0 2 = 1 := by
  have hadd := rrC_add_exp_mul eps 0
  have h1 : rrMass0 eps 0 1 = Real.exp eps * rrC eps 0 := by simp [rrMass0]
  have h2 : rrMass0 eps 0 2 = rrC eps 0 := by simp [rrMass0]
  rw [h1, h2]
  linarith

theorem test_rr_fEpsDelta_zero_half_quarter : fEpsDelta 0 (1/2) (1/4) = 1/4 := by
  have e1 : (1 - (1/2:ℝ) - Real.exp 0 * (1/4)) = 1/4 := by
    rw [Real.exp_zero]
    norm_num
  have e2 : (Real.exp (-(0:ℝ)) * (1 - 1/2 - 1/4) : ℝ) = 1/4 := by
    rw [neg_zero, Real.exp_zero]
    norm_num
  have hmax : max (1/4 : ℝ) (1/4) = 1/4 := test_rr_max_self (1/4)
  show max 0 (max (1 - 1/2 - Real.exp 0 * (1/4))
    (Real.exp (-0) * (1 - 1/2 - 1/4))) = 1/4
  rw [e1, e2, hmax]
  exact max_eq_right (by norm_num)

theorem test_rr_fEpsDelta_delta_one (eps : ℝ) : fEpsDelta eps 1 0 = 0 := by
  have e1 : (1 - (1:ℝ) - Real.exp eps * 0) = 0 := by simp
  have e2 : (Real.exp (-eps) * (1 - 1 - 0) : ℝ) = 0 := by simp
  show max 0 (max (1 - 1 - Real.exp eps * 0)
    (Real.exp (-eps) * (1 - 1 - 0))) = 0
  rw [e1, e2]
  simp only [test_rr_max_self]

theorem test_rr_fEpsDelta_log3_half_zero :
    fEpsDelta (Real.log 3) (1/2) 0 = 1/2 := by
  have e1 : (1 - (1/2:ℝ) - Real.exp (Real.log 3) * 0) = 1/2 := by
    rw [test_rr_exp_log3]
    norm_num
  have e2 : (Real.exp (-Real.log 3) * (1 - 1/2 - 0) : ℝ) = 1/6 := by
    rw [test_rr_exp_neg_log3]
    norm_num
  have hmax : max (1/2 : ℝ) (1/6) = 1/2 := max_eq_left (by norm_num)
  show max 0 (max (1 - 1/2 - Real.exp (Real.log 3) * 0)
    (Real.exp (-Real.log 3) * (1 - 1/2 - 0))) = 1/2
  rw [e1, e2, hmax]
  exact max_eq_right (by norm_num)

theorem test_rr_fEpsDelta_log3_half_eighth :
    fEpsDelta (Real.log 3) (1/2) (1/8) = 1/8 := by
  have e1 : (1 - (1/2:ℝ) - Real.exp (Real.log 3) * (1/8)) = 1/8 := by
    rw [test_rr_exp_log3]
    norm_num
  have e2 : (Real.exp (-Real.log 3) * (1 - 1/2 - 1/8) : ℝ) = 1/8 := by
    rw [test_rr_exp_neg_log3]
    norm_num
  have hmax : max (1/8 : ℝ) (1/8) = 1/8 := test_rr_max_self (1/8)
  show max 0 (max (1 - 1/2 - Real.exp (Real.log 3) * (1/8))
    (Real.exp (-Real.log 3) * (1 - 1/2 - 1/8))) = 1/8
  rw [e1, e2, hmax]
  exact max_eq_right (by norm_num)

theorem test_rr_fEpsDelta_log3_half_half :
    fEpsDelta (Real.log 3) (1/2) (1/2) = 0 := by
  have e1 : (1 - (1/2:ℝ) - Real.exp (Real.log 3) * (1/2)) = -1 := by
    rw [test_rr_exp_log3]
    norm_num
  have e2 : (Real.exp (-Real.log 3) * (1 - 1/2 - 1/2) : ℝ) = 0 := by
    rw [test_rr_exp_neg_log3]
    norm_num
  have hmax : max (-1 : ℝ) 0 = 0 := max_eq_right (by norm_num)
  show max 0 (max (1 - 1/2 - Real.exp (Real.log 3) * (1/2))
    (Real.exp (-Real.log 3) * (1 - 1/2 - 1/2))) = 0
  rw [e1, e2, hmax]
  exact test_rr_max_self 0

theorem test_rr_fEpsDelta_log3_half_one :
    fEpsDelta (Real.log 3) (1/2) 1 = 0 := by
  have e1 : (1 - (1/2:ℝ) - Real.exp (Real.log 3) * 1) = -5/2 := by
    rw [test_rr_exp_log3]
    norm_num
  have e2 : (Real.exp (-Real.log 3) * (1 - 1/2 - 1) : ℝ) = -1/6 := by
    rw [test_rr_exp_neg_log3]
    norm_num
  have hmax : max (-5/2 : ℝ) (-1/6) = -1/6 := max_eq_right (by norm_num)
  show max 0 (max (1 - 1/2 - Real.exp (Real.log 3) * 1)
    (Real.exp (-Real.log 3) * (1 - 1/2 - 1))) = 0
  rw [e1, e2, hmax]
  exact max_eq_left (by norm_num)

theorem test_rr_fEpsDelta_log3_zero_eighth :
    fEpsDelta (Real.log 3) 0 (1/8) = 5/8 := by
  have e1 : (1 - (0:ℝ) - Real.exp (Real.log 3) * (1/8)) = 5/8 := by
    rw [test_rr_exp_log3]
    norm_num
  have e2 : (Real.exp (-Real.log 3) * (1 - 0 - 1/8) : ℝ) = 7/24 := by
    rw [test_rr_exp_neg_log3]
    norm_num
  have hmax : max (5/8 : ℝ) (7/24) = 5/8 := max_eq_left (by norm_num)
  show max 0 (max (1 - 0 - Real.exp (Real.log 3) * (1/8))
    (Real.exp (-Real.log 3) * (1 - 0 - 1/8))) = 5/8
  rw [e1, e2, hmax]
  exact max_eq_right (by norm_num)

theorem test_rr_tradeoff_zero_half_quarter (hδ0 : (0:ℝ) ≤ 1/2)
    (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 0 (1/2) hδ0 hδ1) (rrR1 0 (1/2) hδ0 hδ1)
      (1/4) = 1/4 := by
  rw [rr_tradeoff_eq_fEpsDelta 0 (1/2) (1/4) (by norm_num) hδ0 hδ1
    (by norm_num) (by norm_num)]
  exact test_rr_fEpsDelta_zero_half_quarter

theorem test_rr_tradeoff_delta_one (eps : ℝ) (hε : 0 ≤ eps)
    (hδ0 : (0:ℝ) ≤ 1) (hδ1 : (1:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 eps 1 hδ0 hδ1) (rrR1 eps 1 hδ0 hδ1) 0 = 0 := by
  rw [rr_tradeoff_eq_fEpsDelta eps 1 0 hε hδ0 hδ1 (by norm_num) (by norm_num)]
  exact test_rr_fEpsDelta_delta_one eps

theorem test_rr_tradeoff_log3_half_zero (hδ0 : (0:ℝ) ≤ 1/2)
    (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
      (rrR1 (Real.log 3) (1/2) hδ0 hδ1) 0 = 1/2 := by
  rw [rr_tradeoff_eq_fEpsDelta (Real.log 3) (1/2) 0 test_rr_log3_nonneg hδ0
    hδ1 (by norm_num) (by norm_num)]
  exact test_rr_fEpsDelta_log3_half_zero

theorem test_rr_tradeoff_log3_half_eighth (hδ0 : (0:ℝ) ≤ 1/2)
    (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
      (rrR1 (Real.log 3) (1/2) hδ0 hδ1) (1/8) = 1/8 := by
  rw [rr_tradeoff_eq_fEpsDelta (Real.log 3) (1/2) (1/8) test_rr_log3_nonneg
    hδ0 hδ1 (by norm_num) (by norm_num)]
  exact test_rr_fEpsDelta_log3_half_eighth

theorem test_rr_tradeoff_log3_half_half (hδ0 : (0:ℝ) ≤ 1/2)
    (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
      (rrR1 (Real.log 3) (1/2) hδ0 hδ1) (1/2) = 0 := by
  rw [rr_tradeoff_eq_fEpsDelta (Real.log 3) (1/2) (1/2) test_rr_log3_nonneg
    hδ0 hδ1 (by norm_num) (by norm_num)]
  exact test_rr_fEpsDelta_log3_half_half

theorem test_rr_tradeoff_log3_half_one (hδ0 : (0:ℝ) ≤ 1/2)
    (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
      (rrR1 (Real.log 3) (1/2) hδ0 hδ1) 1 = 0 := by
  rw [rr_tradeoff_eq_fEpsDelta (Real.log 3) (1/2) 1 test_rr_log3_nonneg hδ0
    hδ1 (by norm_num) (by norm_num)]
  exact test_rr_fEpsDelta_log3_half_one

theorem test_rr_bool_kovpair_half :
    KOVpair Bool PH5 QH5 (Real.log 3) (1/2) := by
  rw [kovpair_iff_event_bounds]
  have hev :=
    (kovpair_iff_event_bounds Bool PH5 QH5 (Real.log 3) 0).mp kovpair_PH5_QH5
  intro S
  obtain ⟨h1, h2⟩ := hev S
  exact ⟨by linarith, by linarith⟩

theorem test_rr_tradeoff_bool_eighth : tradeoff Bool PH5 QH5 (1/8 : ℝ) = 5/8 := by
  have hphiT : (fun w => if w = true then (0:ℝ) else 1/2) true = 0 :=
    ite_eq_left rfl
  have hphiF : (fun w => if w = true then (0:ℝ) else 1/2) false = 1/2 :=
    ite_eq_right (by decide : (false : Bool) ≠ true)
  have hphi : IsTest Bool (fun w => if w = true then (0:ℝ) else 1/2) := by
    intro w
    cases w
    · rw [hphiF]
      norm_num
    · rw [hphiT]
      norm_num
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  have hα : alphaOf Bool PH5 (fun w => if w = true then (0:ℝ) else 1/2)
      = 1/8 := by
    simp only [alphaOf, huniv]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [ite_eq_right (by decide : (false : Bool) ≠ true), ite_eq_left rfl,
      PH5_false, PH5_true]
    norm_num
  have hβ : betaOf Bool QH5 (fun w => if w = true then (0:ℝ) else 1/2)
      = 5/8 := by
    simp only [betaOf, huniv]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [ite_eq_right (by decide : (false : Bool) ≠ true), ite_eq_left rfl,
      QH5_false, QH5_true]
    norm_num
  have hub := tradeoff_le_betaOf Bool PH5 QH5 (1/8)
    (fun w => if w = true then (0:ℝ) else 1/2) (by norm_num) hphi (le_of_eq hα)
  rw [hβ] at hub
  have hlow := kovpair_forward_tradeoff_ge Bool PH5 QH5 (Real.log 3) 0 (1/8)
    kovpair_PH5_QH5 (by norm_num) (by norm_num)
  rw [test_rr_fEpsDelta_log3_zero_eighth] at hlow
  exact le_antisymm hub hlow

theorem test_rr_strict_dominance (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
          (rrR1 (Real.log 3) (1/2) hδ0 hδ1) (1/8) = 1/8 ∧
      tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
          (rrR1 (Real.log 3) (1/2) hδ0 hδ1) (1/8) <
        tradeoff Bool PH5 QH5 (1/8) := by
  refine ⟨test_rr_tradeoff_log3_half_eighth hδ0 hδ1, ?_⟩
  rw [test_rr_tradeoff_log3_half_eighth hδ0 hδ1, test_rr_tradeoff_bool_eighth]
  norm_num

theorem test_rr_le_of_kovpair_inst (hδ0 : (0:ℝ) ≤ 1/2) (hδ1 : (1/2:ℝ) ≤ 1) :
    tradeoff (Fin 4) (rrR0 (Real.log 3) (1/2) hδ0 hδ1)
          (rrR1 (Real.log 3) (1/2) hδ0 hδ1) (1/8) ≤
      tradeoff Bool PH5 QH5 (1/8) :=
  rr_tradeoff_le_of_kovpair Bool PH5 QH5 (Real.log 3) (1/2) (1/8) hδ0 hδ1
    test_rr_bool_kovpair_half (by norm_num) (by norm_num)

#print axioms rr_kovpair
#print axioms rr_tradeoff_le_fEpsDelta
#print axioms rr_tradeoff_eq_fEpsDelta
#print axioms rr_tradeoff_le_of_kovpair
