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
