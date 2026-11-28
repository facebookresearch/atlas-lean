/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Privacy.RandomizedResponseDominance

open CSLibExt.Privacy.HypothesisTesting
open CSLibExt.Privacy.DifferentialPrivacy
open scoped BigOperators
open scoped ENNReal

/-!
# Tests for randomized-response dominance under composition

Transcript instances, the `k = 0` and `k = 1` boundaries, the `delta = 0` and
`delta = 1` endpoints, an explicit one-stage channel for the `3/4` vs `1/4`
pair, a pair that no channel reaches, and basic composition recovered through
the reduction.
-/

private lemma h_exp_log_three : Real.exp (Real.log 3) = 3 :=
  Real.exp_log (by norm_num)

private lemma h_exp_neg_log_three : Real.exp (-Real.log 3) = 1 / 3 := by
  have hEE : Real.exp (-Real.log 3) * Real.exp (Real.log 3) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [h_exp_log_three] at hEE
  linarith [hEE]

private lemma h_rrC_log3 : rrC (Real.log 3) 0 = 1 / 4 := by
  unfold rrC
  rw [h_exp_log_three]
  norm_num

private lemma h_fEpsDelta_log3_zero_zero : fEpsDelta (Real.log 3) 0 0 = 1 := by
  unfold fEpsDelta
  rw [h_exp_log_three, h_exp_neg_log_three]
  norm_num

private lemma h_fEpsDelta_log3_half_zero :
    fEpsDelta (Real.log 3) (1 / 2) 0 = 1 / 2 := by
  unfold fEpsDelta
  rw [h_exp_log_three, h_exp_neg_log_three]
  norm_num

private lemma chan0 :
    (![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false] :
      Fin 4 → PMF Bool) 0 = PMF.pure true :=
  rfl

private lemma chan1 :
    (![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false] :
      Fin 4 → PMF Bool) 1 = PMF.pure true :=
  rfl

private lemma chan2 :
    (![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false] :
      Fin 4 → PMF Bool) 2 = PMF.pure false :=
  rfl

private lemma chan3 :
    (![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false] :
      Fin 4 → PMF Bool) 3 = PMF.pure false :=
  rfl

private lemma pure_true_false_toReal : ((PMF.pure true) false).toReal = 0 := by
  simp

private lemma pure_true_true_toReal : ((PMF.pure true) true).toReal = 1 := by
  simp

private lemma pure_false_false_toReal : ((PMF.pure false) false).toReal = 1 := by
  simp

private lemma pure_false_true_toReal : ((PMF.pure false) true).toReal = 0 := by
  simp

/-! ## T1: transcript instances -/

/-- T1a: two four-outcome stages have `16` transcripts. -/
private theorem test_card_transcript_two :
    Fintype.card (Transcript (fun _ => Fin 4) 2) = 16 := by
  rfl

/-- T1b: the decidable equality on transcripts evaluates. -/
private theorem test_transcript_ne :
    (((PUnit.unit, (2 : Fin 4)), (3 : Fin 4)) : Transcript (fun _ => Fin 4) 2) ≠
      (((PUnit.unit, (2 : Fin 4)), (1 : Fin 4)) : Transcript (fun _ => Fin 4) 2) := by
  decide

/-! ## T2: the `k = 0` boundary -/

/-- T2: zero stages carry the unit transcript on both hypotheses. -/
private theorem test_rrKfold_zero (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (b : Bool) : rrKfold eps delta hδ0 hδ1 0 b = PMF.pure PUnit.unit :=
  rfl

/-! ## T3-T4: the `k = 1` boundary -/

/-- T3: one stage of the four-outcome mechanism has tradeoff exactly
`fEpsDelta` on `[0, 1]`, through the carrier `PUnit × Fin 4`. -/
private theorem test_rrKfold_one_tradeoff (eps delta alpha : ℝ) (hε : 0 ≤ eps)
    (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    tradeoff (Transcript (fun _ => Fin 4) 1) (rrKfold eps delta hδ0 hδ1 1 false)
      (rrKfold eps delta hδ0 hδ1 1 true) alpha = fEpsDelta eps delta alpha := by
  have hR0 : rrKfold eps delta hδ0 hδ1 1 false
      = (rrR0 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a) :=
    calc (rrKfold eps delta hδ0 hδ1 1 false :
          PMF (Transcript (fun _ => Fin 4) 1))
        = ((PMF.pure PUnit.unit).bind fun t : Transcript (fun _ => Fin 4) 0 =>
            ((rrStage eps delta hδ0 hδ1 false).bind fun a => PMF.pure (t, a)) :
          PMF (Transcript (fun _ => Fin 4) 1)) := rfl
      _ = ((rrStage eps delta hδ0 hδ1 false).bind fun a =>
            PMF.pure (PUnit.unit, a) : PMF (Transcript (fun _ => Fin 4) 1)) :=
          PMF.pure_bind _ _
      _ = ((rrR0 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a) :
          PMF (Transcript (fun _ => Fin 4) 1)) := rfl
  have hR1 : rrKfold eps delta hδ0 hδ1 1 true
      = (rrR1 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a) :=
    calc (rrKfold eps delta hδ0 hδ1 1 true :
          PMF (Transcript (fun _ => Fin 4) 1))
        = ((PMF.pure PUnit.unit).bind fun t : Transcript (fun _ => Fin 4) 0 =>
            ((rrStage eps delta hδ0 hδ1 true).bind fun a => PMF.pure (t, a)) :
          PMF (Transcript (fun _ => Fin 4) 1)) := rfl
      _ = ((rrStage eps delta hδ0 hδ1 true).bind fun a =>
            PMF.pure (PUnit.unit, a) : PMF (Transcript (fun _ => Fin 4) 1)) :=
          PMF.pure_bind _ _
      _ = ((rrR1 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a) :
          PMF (Transcript (fun _ => Fin 4) 1)) := rfl
  have hpost1 := tradeoff_postprocess (Fin 4) (Transcript (fun _ => Fin 4) 1)
    (rrR0 eps delta hδ0 hδ1) (rrR1 eps delta hδ0 hδ1)
    (fun a => PMF.pure (PUnit.unit, a)) alpha hα0 hα1
  have e1 : tradeoff (Transcript (fun _ => Fin 4) 1)
      ((rrR0 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a))
      ((rrR1 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a)) alpha
      = tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold eps delta hδ0 hδ1 1 false)
        (rrKfold eps delta hδ0 hδ1 1 true) alpha :=
    congrArg₂ (fun P Q => tradeoff (Transcript (fun _ => Fin 4) 1) P Q alpha)
      hR0.symm hR1.symm
  have hle1 : tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
      (rrR1 eps delta hδ0 hδ1) alpha
      ≤ tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold eps delta hδ0 hδ1 1 false)
        (rrKfold eps delta hδ0 hδ1 1 true) alpha :=
    calc tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
          (rrR1 eps delta hδ0 hδ1) alpha
        ≤ tradeoff (Transcript (fun _ => Fin 4) 1)
            ((rrR0 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a))
            ((rrR1 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a))
            alpha := hpost1
      _ = tradeoff (Transcript (fun _ => Fin 4) 1)
            (rrKfold eps delta hδ0 hδ1 1 false)
            (rrKfold eps delta hδ0 hδ1 1 true) alpha := e1
  have hpt : ∀ a : Fin 4,
      ((PMF.pure (PUnit.unit, a)).bind fun t : Transcript (fun _ => Fin 4) 1 =>
        PMF.pure t.2) = PMF.pure a := fun a => PMF.pure_bind _ _
  have g0 : ((rrKfold eps delta hδ0 hδ1 1 false).bind fun t => PMF.pure t.2)
      = rrR0 eps delta hδ0 hδ1 :=
    calc ((rrKfold eps delta hδ0 hδ1 1 false).bind fun t => PMF.pure t.2)
        = (((rrR0 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a)).bind
          fun t => PMF.pure t.2) :=
          congrArg (fun P => P.bind (fun t : Transcript (fun _ => Fin 4) 1 =>
            PMF.pure t.2)) hR0
      _ = (rrR0 eps delta hδ0 hδ1).bind (fun a =>
          ((PMF.pure (PUnit.unit, a)).bind fun t : Transcript (fun _ => Fin 4) 1 =>
            PMF.pure t.2)) := PMF.bind_bind _ _ _
      _ = (rrR0 eps delta hδ0 hδ1).bind (fun a => PMF.pure a) :=
          congrArg _ (funext hpt)
      _ = rrR0 eps delta hδ0 hδ1 := PMF.bind_pure _
  have g1 : ((rrKfold eps delta hδ0 hδ1 1 true).bind fun t => PMF.pure t.2)
      = rrR1 eps delta hδ0 hδ1 :=
    calc ((rrKfold eps delta hδ0 hδ1 1 true).bind fun t => PMF.pure t.2)
        = (((rrR1 eps delta hδ0 hδ1).bind fun a => PMF.pure (PUnit.unit, a)).bind
          fun t => PMF.pure t.2) :=
          congrArg (fun P => P.bind (fun t : Transcript (fun _ => Fin 4) 1 =>
            PMF.pure t.2)) hR1
      _ = (rrR1 eps delta hδ0 hδ1).bind (fun a =>
          ((PMF.pure (PUnit.unit, a)).bind fun t : Transcript (fun _ => Fin 4) 1 =>
            PMF.pure t.2)) := PMF.bind_bind _ _ _
      _ = (rrR1 eps delta hδ0 hδ1).bind (fun a => PMF.pure a) :=
          congrArg _ (funext hpt)
      _ = rrR1 eps delta hδ0 hδ1 := PMF.bind_pure _
  have hpost2 := tradeoff_postprocess (Transcript (fun _ => Fin 4) 1) (Fin 4)
    (rrKfold eps delta hδ0 hδ1 1 false) (rrKfold eps delta hδ0 hδ1 1 true)
    (fun t => PMF.pure t.2) alpha hα0 hα1
  have e2 : tradeoff (Fin 4)
      ((rrKfold eps delta hδ0 hδ1 1 false).bind fun t => PMF.pure t.2)
      ((rrKfold eps delta hδ0 hδ1 1 true).bind fun t => PMF.pure t.2) alpha
      = tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
        (rrR1 eps delta hδ0 hδ1) alpha :=
    congrArg₂ (fun P Q => tradeoff (Fin 4) P Q alpha) g0 g1
  have hle2 : tradeoff (Transcript (fun _ => Fin 4) 1)
      (rrKfold eps delta hδ0 hδ1 1 false)
      (rrKfold eps delta hδ0 hδ1 1 true) alpha
      ≤ tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
        (rrR1 eps delta hδ0 hδ1) alpha :=
    calc tradeoff (Transcript (fun _ => Fin 4) 1)
          (rrKfold eps delta hδ0 hδ1 1 false)
          (rrKfold eps delta hδ0 hδ1 1 true) alpha
        ≤ tradeoff (Fin 4)
            ((rrKfold eps delta hδ0 hδ1 1 false).bind fun t => PMF.pure t.2)
            ((rrKfold eps delta hδ0 hδ1 1 true).bind fun t => PMF.pure t.2)
            alpha := hpost2
      _ = tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
          (rrR1 eps delta hδ0 hδ1) alpha := e2
  have hrr := rr_tradeoff_eq_fEpsDelta eps delta alpha hε hδ0 hδ1 hα0 hα1
  apply le_antisymm
  · calc tradeoff (Transcript (fun _ => Fin 4) 1)
            (rrKfold eps delta hδ0 hδ1 1 false)
            (rrKfold eps delta hδ0 hδ1 1 true) alpha
          ≤ tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
            (rrR1 eps delta hδ0 hδ1) alpha := hle2
        _ = fEpsDelta eps delta alpha := hrr
  · calc fEpsDelta eps delta alpha
          = tradeoff (Fin 4) (rrR0 eps delta hδ0 hδ1)
            (rrR1 eps delta hδ0 hδ1) alpha := hrr.symm
        _ ≤ tradeoff (Transcript (fun _ => Fin 4) 1)
            (rrKfold eps delta hδ0 hδ1 1 false)
            (rrKfold eps delta hδ0 hδ1 1 true) alpha := hle1

/-- T4: `k = 1` instance of the dominance for the `3/4` vs `1/4` pair. -/
private theorem test_rrKfold_one_PH5 (alpha : ℝ) (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold (Real.log 3) 0 le_rfl zero_le_one 1 false)
        (rrKfold (Real.log 3) 0 le_rfl zero_le_one 1 true) alpha ≤
      tradeoff (Transcript (fun _ => Bool) 1)
        (kfoldCompose (fun _ _ b => cond b QH5 PH5) 1 false)
        (kfoldCompose (fun _ _ b => cond b QH5 PH5) 1 true) alpha :=
  rrKfold_tradeoff_le (fun _ _ b => cond b QH5 PH5) false true (Real.log 3) 0 alpha 1
    (Real.log_nonneg (by norm_num)) le_rfl zero_le_one
    (fun _ _ _ => kovpair_PH5_QH5) hα0 hα1

/-! ## T5: the `delta = 0` endpoint -/

/-- T5a: `k` stages of the four-outcome mechanism are `(k * eps, k * delta)`-DP,
from `isApproxDP_kfold_const`. -/
private theorem test_rrKfold_basic (eps delta : ℝ) (k : ℕ) (hε : 0 ≤ eps)
    (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    IsApproxDP (rrKfold eps delta hδ0 hδ1 k) (fun b b' => b ≠ b')
      (k * eps) (k * delta) := by
  have h := isApproxDP_kfold_const (M := fun _ => rrStage eps delta hδ0 hδ1)
    (ε := fun _ => eps) (δ := fun _ => delta) k
    (fun i _ => hε) (fun i _ => hδ0)
    (fun i _ => isApproxDP_rrStage eps delta hε hδ0 hδ1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact h

/-- T5b: at `delta = 0` the reduction gives `(k * eps, 0)` for every adaptive
composition of `(eps, 0)`-DP stages. -/
private theorem test_reduction_pure {D : Type*} {A : ℕ → Type}
    [∀ n, Finite (A n)] {adj : D → D → Prop} [Std.Symm adj]
    (K : (n : ℕ) → Transcript A n → D → PMF (A n)) (eps : ℝ) (k : ℕ)
    (hε : 0 ≤ eps)
    (hK : ∀ i, i < k → ∀ t, IsApproxDP (fun d => K i t d) adj eps 0) :
    IsApproxDP (kfoldCompose K k) adj (k * eps) 0 := by
  have hRR := test_rrKfold_basic eps 0 k hε le_rfl zero_le_one
  rw [mul_zero] at hRR
  exact isApproxDP_kfold_of_rrKfold K eps 0 (k * eps) 0 k hε le_rfl zero_le_one hK hRR

/-- T5c: an explicit channel from the four-outcome pair at `(log 3, 0)` to the
`3/4` vs `1/4` pair, checked without `rr_exists_channel_of_kovpair`. -/
private theorem test_channel_PH5_QH5 :
    (rrR0 (Real.log 3) 0 le_rfl zero_le_one).bind
        ![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false] = PH5 ∧
      (rrR1 (Real.log 3) 0 le_rfl zero_le_one).bind
        ![PMF.pure true, PMF.pure true, PMF.pure false, PMF.pure false] = QH5 := by
  have hexp : Real.exp (Real.log 3) = 3 := h_exp_log_three
  have hc : rrC (Real.log 3) 0 = 1 / 4 := h_rrC_log3
  constructor
  · apply PMF.ext
    intro y
    cases y
    case false =>
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · rw [pmf_bind_toReal, Fin.sum_univ_four, rrR0_toReal_zero,
          rrR0_toReal_one, rrR0_toReal_two, rrR0_toReal_three, chan0, chan1,
          chan2, chan3, PH5_false, hexp, hc]
        norm_num [pure_true_false_toReal, pure_false_false_toReal]
    case true =>
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · rw [pmf_bind_toReal, Fin.sum_univ_four, rrR0_toReal_zero,
          rrR0_toReal_one, rrR0_toReal_two, rrR0_toReal_three, chan0, chan1,
          chan2, chan3, PH5_true, hexp, hc]
        norm_num [pure_true_true_toReal, pure_false_true_toReal]
  · apply PMF.ext
    intro y
    cases y
    case false =>
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · rw [pmf_bind_toReal, Fin.sum_univ_four, rrR1_toReal_zero,
          rrR1_toReal_one, rrR1_toReal_two, rrR1_toReal_three, chan0, chan1,
          chan2, chan3, QH5_false, hexp, hc]
        norm_num [pure_true_false_toReal, pure_false_false_toReal]
    case true =>
      refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · exact ne_of_lt (PMF.apply_lt_top _ _)
      · rw [pmf_bind_toReal, Fin.sum_univ_four, rrR1_toReal_zero,
          rrR1_toReal_one, rrR1_toReal_two, rrR1_toReal_three, chan0, chan1,
          chan2, chan3, QH5_true, hexp, hc]
        norm_num [pure_true_true_toReal, pure_false_true_toReal]

/-- T5d: the same pair through the theorem. -/
private theorem test_channel_PH5_QH5_exists :
    ∃ T : Fin 4 → PMF Bool,
      (rrR0 (Real.log 3) 0 le_rfl zero_le_one).bind T = PH5 ∧
        (rrR1 (Real.log 3) 0 le_rfl zero_le_one).bind T = QH5 :=
  rr_exists_channel_of_kovpair Bool PH5 QH5 (Real.log 3) 0
    (Real.log_nonneg (by norm_num)) le_rfl zero_le_one kovpair_PH5_QH5

/-! ## T6: the `KOVpair` hypothesis is needed -/

/-- T6: no channel maps the four-outcome pair at `(log 3, 0)` to the point
masses at `true` and `false`, which are not `(log 3, 0)`-indistinguishable. -/
private theorem test_no_channel_point_masses :
    ¬ ∃ T : Fin 4 → PMF Bool,
      (rrR0 (Real.log 3) 0 le_rfl zero_le_one).bind T = PMF.pure true ∧
        (rrR1 (Real.log 3) 0 le_rfl zero_le_one).bind T = PMF.pure false := by
  intro hEx
  obtain ⟨T, hT0, hT1⟩ := hEx
  have hpost := tradeoff_postprocess (Fin 4) Bool
    (rrR0 (Real.log 3) 0 le_rfl zero_le_one)
    (rrR1 (Real.log 3) 0 le_rfl zero_le_one) T 0 le_rfl zero_le_one
  rw [hT0, hT1] at hpost
  have hLHS : tradeoff (Fin 4) (rrR0 (Real.log 3) 0 le_rfl zero_le_one)
      (rrR1 (Real.log 3) 0 le_rfl zero_le_one) 0 = 1 := by
    have h := rr_tradeoff_eq_fEpsDelta (Real.log 3) 0 0
      (Real.log_nonneg (by norm_num)) le_rfl zero_le_one le_rfl zero_le_one
    exact h.trans h_fEpsDelta_log3_zero_zero
  have hRHS : tradeoff Bool (PMF.pure true) (PMF.pure false) 0 = 0 := by
    apply le_antisymm
    · have hub :=
        tradeoff_indicator_upper Bool (PMF.pure true) (PMF.pure false) {false}
      have hI : typeI Bool (PMF.pure true) {false} = 0 := by simp [typeI]
      have hII : typeII Bool (PMF.pure false) {false} = 0 := by
        have hc : ({false} : Finset Bool)ᶜ = {true} := by decide
        simp [typeII, hc]
      rw [hI, hII] at hub
      exact hub
    · exact le_tradeoff Bool (PMF.pure true) (PMF.pure false) 0 0 le_rfl
        (fun phi hphi _ => betaOf_nonneg Bool (PMF.pure false) phi hphi)
  rw [hLHS, hRHS] at hpost
  norm_num at hpost

/-! ## T7: the `delta = 1` endpoint -/

/-- T7: at `delta = 1` every pair is the image of the four-outcome pair. -/
private theorem test_channel_delta_one (eps : ℝ) (hε : 0 ≤ eps) (P Q : PMF Bool) :
    ∃ T : Fin 4 → PMF Bool,
      (rrR0 eps 1 zero_le_one le_rfl).bind T = P ∧
        (rrR1 eps 1 zero_le_one le_rfl).bind T = Q := by
  refine rr_exists_channel_of_kovpair Bool P Q eps 1 hε zero_le_one le_rfl ?_
  intro S
  have hI := typeI_nonneg Bool P S
  have hII : 0 ≤ typeII Bool Q S := by
    simp only [typeII]
    apply Finset.sum_nonneg
    intro w _
    exact ENNReal.toReal_nonneg
  have hE : 0 ≤ Real.exp eps := (Real.exp_pos eps).le
  have h11 : (1 : ℝ) - 1 = 0 := by norm_num
  rw [h11]
  constructor
  · exact add_nonneg hI (mul_nonneg hE hII)
  · exact add_nonneg (mul_nonneg hE hI) hII

/-! ## T8-T9: the stage parameters matter -/

/-- T8: at `alpha = 0` one stage at `(log 3, 1/2)` has tradeoff `1/2`, and one
stage at `(log 3, 0)` has tradeoff `1`. -/
private theorem test_rrKfold_one_delta_values :
    tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold (Real.log 3) (1 / 2) (by norm_num) (by norm_num) 1 false)
        (rrKfold (Real.log 3) (1 / 2) (by norm_num) (by norm_num) 1 true) 0 = 1 / 2 ∧
      tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold (Real.log 3) 0 le_rfl zero_le_one 1 false)
        (rrKfold (Real.log 3) 0 le_rfl zero_le_one 1 true) 0 = 1 := by
  constructor
  · have h := test_rrKfold_one_tradeoff (Real.log 3) (1 / 2) 0
      (Real.log_nonneg (by norm_num)) (by norm_num) (by norm_num) le_rfl
      zero_le_one
    exact h.trans h_fEpsDelta_log3_half_zero
  · have h := test_rrKfold_one_tradeoff (Real.log 3) 0 0
      (Real.log_nonneg (by norm_num)) le_rfl zero_le_one le_rfl zero_le_one
    exact h.trans h_fEpsDelta_log3_zero_zero

/-- T9: dominance needs the stage parameters: one stage at `(log 3, 0)` does not
lie below one stage at `(log 3, 1/2)`, itself a one-fold composition of
`(log 3, 1/2)`-stages. -/
private theorem test_dominance_needs_delta :
    ¬ tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold (Real.log 3) 0 le_rfl zero_le_one 1 false)
        (rrKfold (Real.log 3) 0 le_rfl zero_le_one 1 true) 0 ≤
      tradeoff (Transcript (fun _ => Fin 4) 1)
        (rrKfold (Real.log 3) (1 / 2) (by norm_num) (by norm_num) 1 false)
        (rrKfold (Real.log 3) (1 / 2) (by norm_num) (by norm_num) 1 true) 0 := by
  obtain ⟨h1, h2⟩ := test_rrKfold_one_delta_values
  rw [h1, h2]
  norm_num

#print axioms rr_exists_channel_of_kovpair
#print axioms isApproxDP_rrStage
#print axioms rrKfold_exists_channel
#print axioms rrKfold_tradeoff_le
#print axioms kovpair_kfold_of_rrKfold
#print axioms isApproxDP_kfold_of_rrKfold
