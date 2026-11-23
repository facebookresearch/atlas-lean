/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Privacy.ApproximateDifferentialPrivacy
import Cslib.Probability.PMF

/-!
# Approximate-DP clients and refutations

Concrete normalized PMFs exercise the public API. Countermodels reject
incorrect alternatives; none is used as an assumption in production.
-/

open CSLibExt.Privacy.DifferentialPrivacy
open Cslib.Probability.PMF
open scoped ENNReal NNReal

namespace CSLibExtTest.Privacy.ApproximateDifferentialPrivacy

private theorem bool_private {D : Type*} {M : D → PMF Bool}
    {adj : D → D → Prop} {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (h : ∀ d d', adj d d' → ∀ b,
      M d b ≤ ENNReal.ofReal (Real.exp ε) * M d' b + ENNReal.ofReal δ) :
    IsApproxDP M adj ε δ := by
  classical
  refine ⟨hε, hδ, fun d d' ha s => ?_⟩
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp ε) := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (Real.one_le_exp hε)
  have hs : s = ∅ ∨ s = {false} ∨ s = {true} ∨ s = Set.univ := by
    by_cases hf : false ∈ s <;> by_cases ht : true ∈ s
    · exact Or.inr (Or.inr (Or.inr
        (Set.ext fun b => by cases b <;> simp [hf, ht])))
    · exact Or.inr (Or.inl (Set.ext fun b => by cases b <;> simp [hf, ht]))
    · exact Or.inr (Or.inr (Or.inl
        (Set.ext fun b => by cases b <;> simp [hf, ht])))
    · exact Or.inl (Set.ext fun b => by cases b <;> simp [hf, ht])
  rcases hs with rfl | rfl | rfl | rfl
  · simp
  · simpa only [PMF.toOuterMeasure_apply_singleton] using h d d' ha false
  · simpa only [PMF.toOuterMeasure_apply_singleton] using h d d' ha true
  · simpa only [PMF.toOuterMeasure_apply, Set.indicator_univ,
      PMF.tsum_coe, mul_one] using hc.trans le_self_add

private noncomputable def fifths (d : Bool) : PMF Bool :=
  PMF.ofFintype (fun b => ((if b = d then 3 / 5 else 2 / 5 : ℝ≥0) : ℝ≥0∞))
    (by norm_cast; cases d <;> norm_num)

private theorem fifths_private :
    IsApproxDP fifths (fun _ _ => True) 0 (1 / 5) := by
  apply bool_private (by norm_num) (by norm_num)
  intro d d' _ b
  have hd : ENNReal.ofReal (1 / 5 : ℝ) = ((1 / 5 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    rfl
  have hn : (if b = d then 3 / 5 else 2 / 5 : ℝ≥0) ≤
      (if b = d' then 3 / 5 else 2 / 5) + 1 / 5 := by
    cases d <;> cases d' <;> cases b <;> norm_num [← NNReal.coe_le_coe]
  simpa only [fifths, PMF.ofFintype_apply, Real.exp_zero,
    ENNReal.ofReal_one, one_mul, hd, ← ENNReal.coe_add] using
    ENNReal.coe_le_coe.mpr hn

private theorem uninformative {D A : Type*} (M : D → PMF A)
    (adj : D → D → Prop) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 1 ≤ δ) :
    IsApproxDP M adj ε δ := by
  refine ⟨hε, le_trans (by norm_num) hδ, fun d d' _ s => ?_⟩
  have hp : (M d).toOuterMeasure s ≤ 1 := by
    rw [PMF.toOuterMeasure_apply, ← (M d).tsum_coe]
    exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self s (M d) a
  have hd : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hδ
  exact (hp.trans hd).trans le_add_self

private theorem identity_and_constant_boundaries :
    IsApproxDP (fun d : Bool => PMF.pure d) (fun _ _ => True) 0 1 ∧
    IsApproxDP (fun d : Bool => PMF.pure d) (fun _ _ => True) 1 2 ∧
    ¬IsApproxDP (fun d : Bool => PMF.pure d) (fun _ _ => True) 0 0 ∧
    IsApproxDP (fun _ : Bool => PMF.pure false) (fun _ _ => True) 0 0 ∧
    (PMF.pure false : PMF Bool) true = 0 := by
  refine ⟨uninformative _ _ (by norm_num) (by norm_num),
    uninformative _ _ (by norm_num) (by norm_num), ?_,
    isApproxDP_zero_iff.mpr (isDP_const _ _), by simp⟩
  intro h
  have bad := (isApproxDP_zero_iff.mp h).2 false true trivial false
  norm_num [PMF.pure_apply] at bad

private theorem empty_and_negative_budgets :
    let M : Empty → PMF Empty := Empty.elim
    let K : Empty → Empty → PMF Bool := fun a => a.elim
    IsApproxDP M (fun _ _ => True) 0 0 ∧
    ¬IsApproxDP M (fun _ _ => False) (-1) 0 ∧
    ¬IsApproxDP M (fun _ _ => False) 0 (-1) ∧
    (∀ a, IsApproxDP (K a) (fun _ _ => True) (-1) 0) ∧
    (∀ a, IsApproxDP (K a) (fun _ _ => True) 0 (-1)) ∧
    ¬IsApproxDP (fun d => (M d).bind fun a =>
      (K a d).bind fun b => PMF.pure (a, b)) (fun _ _ => True) (0 + -1) 0 ∧
    ¬IsApproxDP (fun d => (M d).bind fun a =>
      (K a d).bind fun b => PMF.pure (a, b)) (fun _ _ => True) 0 (0 + -1) := by
  refine ⟨⟨le_rfl, le_rfl, fun d => d.elim⟩, ?_, ?_,
    (fun a => a.elim), (fun a => a.elim), ?_, ?_⟩
  all_goals intro h
  · exact (by norm_num : ¬(0 : ℝ) ≤ -1) h.1
  · exact (by norm_num : ¬(0 : ℝ) ≤ -1) h.2.1
  · exact (by norm_num : ¬(0 : ℝ) ≤ 0 + -1) h.1
  · exact (by norm_num : ¬(0 : ℝ) ≤ 0 + -1) h.2.1

private theorem ordered_randomized_postprocessing :
    IsApproxDP (fun d => (fifths d).bind fifths)
      (fun d d' => d = false ∧ d' = true) 0 (1 / 5) ∧
    ¬(true = false ∧ false = true) ∧
    (fifths false).bind fifths false = ((13 / 25 : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨isApproxDP_bind ⟨fifths_private.1, fifths_private.2.1,
    fun d d' _ s => fifths_private.2.2 d d' trivial s⟩ fifths,
    by decide, ?_⟩
  rw [PMF.bind_apply, tsum_fintype]
  simp only [Fintype.sum_bool, fifths, PMF.ofFintype_apply,
    Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
    ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_inj]
  norm_num

private theorem bounded_test_and_many_to_one :
    (∑' b, fifths false b * (if b then 1 / 2 else 1)) ≤
      (∑' b, fifths true b * (if b then 1 / 2 else 1)) +
        ENNReal.ofReal (1 / 5) ∧
    IsApproxDP (fun d => (fifths d).bind (fun _ => PMF.pure ()))
      (fun _ _ => True) 0 (1 / 5) ∧
    (fifths false).bind (fun _ => PMF.pure ()) () = 1 ∧
    IsApproxDP (fun d : Empty => (d.elim : PMF Empty).bind fun a =>
      (a.elim : PMF Bool).bind fun b => PMF.pure (a, b))
      (fun _ _ => True) (0 + 1) (0 + 2) := by
  refine ⟨?_, isApproxDP_bind fifths_private _, by simp, ?_⟩
  · simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (isApproxDP_iff_bounded_test.mp fifths_private).2.2 false true trivial
        (fun b => if b then 1 / 2 else 1)
        (fun b => by cases b <;> norm_num)
  · exact isApproxDP_comp_bind_pair
      ⟨le_rfl, le_rfl, fun d => d.elim⟩ (by norm_num) (by norm_num)
      (fun a => a.elim)

private noncomputable def quarters (d : Bool) : PMF Bool :=
  PMF.ofFintype (fun b => ((if b = d then 3 / 4 else 1 / 4 : ℝ≥0) : ℝ≥0∞))
    (by norm_cast; cases d <;> norm_num)

private theorem quarters_private :
    IsApproxDP quarters (fun _ _ => True) (Real.log 2) (1 / 4) := by
  apply bool_private (Real.log_nonneg (by norm_num)) (by norm_num)
  intro d d' _ b
  have hd : ENNReal.ofReal (1 / 4 : ℝ) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    rfl
  have hn : (if b = d then 3 / 4 else 1 / 4 : ℝ≥0) ≤
      2 * (if b = d' then 3 / 4 else 1 / 4) + 1 / 4 := by
    cases d <;> cases d' <;> cases b <;> norm_num [← NNReal.coe_le_coe]
  simpa only [quarters, PMF.ofFintype_apply,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_ofNat, hd, ENNReal.coe_add, ENNReal.coe_mul,
    ENNReal.coe_ofNat] using ENNReal.coe_le_coe.mpr hn

private noncomputable def adaptiveTranscript (d : Bool) : PMF (Bool × Bool) :=
  (fifths d).bind fun a =>
    (quarters (Bool.xor a d)).bind fun b => PMF.pure (a, b)

private theorem adaptive_distinct_budgets :
    IsApproxDP adaptiveTranscript (fun _ _ => True)
      (0 + Real.log 2) (1 / 5 + 1 / 4) ∧
    adaptiveTranscript false (false, false) = ((9 / 20 : ℝ≥0) : ℝ≥0∞) ∧
    adaptiveTranscript true (false, false) = ((1 / 10 : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨isApproxDP_comp_bind_pair fifths_private quarters_private.1
    quarters_private.2.1 (fun a => ⟨quarters_private.1,
      quarters_private.2.1, fun d d' _ s =>
        quarters_private.2.2 (Bool.xor a d) (Bool.xor a d') trivial s⟩), ?_⟩
  constructor <;>
    simp only [adaptiveTranscript, bind_pair_apply, fifths, quarters,
      PMF.ofFintype_apply, Bool.false_xor, Bool.false_eq_true,
      ite_true, ite_false, ← ENNReal.coe_mul, ENNReal.coe_inj] <;> norm_num

private noncomputable def splitFifths (d : Bool) : PMF (Bool × Bool) :=
  (fifths d).bind fun a =>
    (uniformOfFintype Bool).bind fun b => PMF.pure (a, b)

private theorem splitFifths_apply (d a b : Bool) :
    splitFifths d (a, b) =
      (((if a = d then 3 / 5 else 2 / 5) * (1 / 2) : ℝ≥0) : ℝ≥0∞) := by
  rw [splitFifths, bind_pair_apply]
  simp only [fifths, PMF.ofFintype_apply, uniformOfFintype_apply,
    Fintype.card_bool, ENNReal.coe_mul, one_div,
    ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0)]
  norm_num

private theorem singleton_delta_not_event_delta :
    IsApproxDP splitFifths (fun _ _ => True) 0 (1 / 5) ∧
    (∀ d d' ab, splitFifths d ab ≤
      splitFifths d' ab + ENNReal.ofReal (1 / 10)) ∧
    ¬IsApproxDP splitFifths (fun _ _ => True) 0 (1 / 10) := by
  have hd : ENNReal.ofReal (1 / 10 : ℝ) = ((1 / 10 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    rfl
  refine ⟨isApproxDP_bind fifths_private _, ?_, ?_⟩
  · intro d d' ⟨a, b⟩
    rw [splitFifths_apply, splitFifths_apply, hd, ← ENNReal.coe_add]
    apply ENNReal.coe_le_coe.mpr
    cases d <;> cases d' <;> cases a <;> norm_num [← NNReal.coe_le_coe]
  · intro h
    have hp := isApproxDP_bind h (fun ab => PMF.pure ab.1)
    have hm : IsApproxDP fifths (fun _ _ => True) 0 (1 / 10) := by
      simpa only [splitFifths, PMF.bind_bind, PMF.pure_bind,
        PMF.bind_const, PMF.bind_pure] using hp
    have bad := hm.2.2 false true trivial {false}
    simp only [PMF.toOuterMeasure_apply_singleton, fifths, PMF.ofFintype_apply,
      Real.exp_zero, ENNReal.ofReal_one, one_mul, hd, ite_true,
      Bool.false_eq_true, ite_false, ← ENNReal.coe_add] at bad
    have hn := ENNReal.coe_le_coe.mp bad
    norm_num [← NNReal.coe_le_coe] at hn

private noncomputable def rare (d : Bool) : PMF Bool :=
  PMF.ofFintype (fun b => ((if d then (if b then 0 else 1)
    else (if b then 1 / 4 else 3 / 4) : ℝ≥0) : ℝ≥0∞))
      (by norm_cast; cases d <;> norm_num)

private theorem rare_private :
    IsApproxDP rare (fun _ _ => True) 0 (1 / 4) := by
  apply bool_private (by norm_num) (by norm_num)
  intro d d' _ b
  have hd : ENNReal.ofReal (1 / 4 : ℝ) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    rfl
  simp only [rare, PMF.ofFintype_apply, Real.exp_zero,
    ENNReal.ofReal_one, one_mul, hd, ← ENNReal.coe_add]
  apply ENNReal.coe_le_coe.mpr
  cases d <;> cases d' <;> cases b <;> norm_num [← NNReal.coe_le_coe]

private noncomputable def rareJoint (d : Bool) : PMF (Bool × Bool) :=
  (rare d).bind fun a => (rare d).bind fun b => PMF.pure (a, b)

private theorem rareJoint_event (d : Bool) :
    (rareJoint d).toOuterMeasure {ab | ab.1 = true ∨ ab.2 = true} =
      ((if d then 0 else 7 / 16 : ℝ≥0) : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  cases d <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator_apply,
      Set.mem_ofPred_eq, Bool.false_eq_true, or_self, or_true, true_or,
      ite_true, ite_false, rareJoint, bind_pair_apply, rare,
      PMF.ofFintype_apply, ← ENNReal.coe_zero,
      ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_inj] <;> norm_num

private theorem max_delta_refuted :
    IsApproxDP rareJoint (fun _ _ => True) (0 + 0) (1 / 4 + 1 / 4) ∧
    ¬IsApproxDP rareJoint (fun _ _ => True) 0 (max (1 / 4) (1 / 4)) := by
  refine ⟨isApproxDP_comp_bind_pair rare_private (by norm_num)
    (by norm_num) (fun _ => rare_private), ?_⟩
  intro h
  have bad := h.2.2 false true trivial {ab | ab.1 = true ∨ ab.2 = true}
  have hd : ENNReal.ofReal (1 / 4 : ℝ) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num)]
    rfl
  simp only [rareJoint_event, ite_true, ENNReal.coe_zero,
    mul_zero, zero_add, max_self, hd] at bad
  have hn := ENNReal.coe_le_coe.mp bad
  norm_num [← NNReal.coe_le_coe] at hn

private noncomputable def thirds (d : Bool) : PMF Bool :=
  PMF.ofFintype (fun b => ((if b = d then 2 / 3 else 1 / 3 : ℝ≥0) : ℝ≥0∞))
    (by norm_cast; cases d <;> norm_num)

private theorem pure_stages :
    IsApproxDP thirds (fun _ _ => True) (Real.log 2) 0 ∧
    IsApproxDP quarters (fun _ _ => True) (Real.log 3) 0 := by
  constructor
  · apply isApproxDP_zero_iff.mpr
    refine ⟨Real.log_nonneg (by norm_num), fun d d' _ b => ?_⟩
    rw [Real.exp_log (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    change ((if b = d then 2 / 3 else 1 / 3 : ℝ≥0) : ℝ≥0∞) ≤
      ((2 * (if b = d' then 2 / 3 else 1 / 3) : ℝ≥0) : ℝ≥0∞)
    apply ENNReal.coe_le_coe.mpr
    cases d <;> cases d' <;> cases b <;> norm_num [← NNReal.coe_le_coe]
  · apply isApproxDP_zero_iff.mpr
    refine ⟨Real.log_nonneg (by norm_num), fun d d' _ b => ?_⟩
    rw [Real.exp_log (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    change ((if b = d then 3 / 4 else 1 / 4 : ℝ≥0) : ℝ≥0∞) ≤
      ((3 * (if b = d' then 3 / 4 else 1 / 4) : ℝ≥0) : ℝ≥0∞)
    apply ENNReal.coe_le_coe.mpr
    cases d <;> cases d' <;> cases b <;> norm_num [← NNReal.coe_le_coe]

private theorem max_epsilon_refuted :
    let J := fun d => (thirds d).bind fun a =>
      (quarters d).bind fun b => PMF.pure (a, b)
    IsApproxDP J (fun _ _ => True) (Real.log 2 + Real.log 3) 0 ∧
    IsDP J (fun _ _ => True) (Real.log 2 + Real.log 3) ∧
    ¬IsApproxDP J (fun _ _ => True) (max (Real.log 2) (Real.log 3)) 0 := by
  dsimp only
  have hp := isApproxDP_comp_bind_pair pure_stages.1 pure_stages.2.1
    pure_stages.2.2.1 (fun _ => pure_stages.2)
  simp only [add_zero] at hp
  refine ⟨hp, isApproxDP_zero_iff.mp hp, ?_⟩
  intro h
  have bad := (isApproxDP_zero_iff.mp h).2 false true trivial (false, false)
  rw [max_eq_right (Real.log_le_log (by norm_num) (by norm_num)),
    Real.exp_log (by norm_num)] at bad
  simp only [bind_pair_apply, thirds, quarters, PMF.ofFintype_apply,
    ite_true, Bool.false_eq_true, ite_false, ENNReal.ofReal_ofNat] at bad
  have hn : (2 / 3 : ℝ≥0) * (3 / 4) ≤ 3 * ((1 / 3) * (1 / 4)) := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat] using bad
  norm_num [← NNReal.coe_le_coe] at hn

private theorem bad_output_gloss_refuted :
    IsApproxDP fifths (fun _ _ => True) 0 (1 / 5) ∧
    (fifths false).toOuterMeasure
      {b | 0 < |Real.log
        ((fifths false b).toReal / (fifths true b).toReal)|} = 1 ∧
    ENNReal.ofReal (1 / 5 : ℝ) < 1 := by
  have hl : ∀ b, Real.log ((fifths false b).toReal /
      (fifths true b).toReal) ≠ 0 := by
    intro b
    cases b <;> apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num [fifths]
  have hs : {b | 0 < |Real.log ((fifths false b).toReal /
      (fifths true b).toReal)|} = Set.univ :=
    Set.eq_univ_of_forall (fun b => abs_pos.mpr (hl b))
  refine ⟨fifths_private, ?_, ?_⟩
  · rw [hs, PMF.toOuterMeasure_apply]
    simp only [Set.indicator_univ, PMF.tsum_coe]
  · rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

private theorem setwise_positive_part_refuted :
    let ν := fun s : Set Bool =>
      (fifths false).toOuterMeasure s - (fifths true).toOuterMeasure s
    IsApproxDP fifths (fun _ _ => True) 0 (1 / 5) ∧
    Disjoint ({false} : Set Bool) {true} ∧
    ν ({false} ∪ {true}) ≠ ν {false} + ν {true} := by
  dsimp only
  refine ⟨fifths_private, by simp, ?_⟩
  have hs : ({false} : Set Bool) ∪ {true} = Set.univ := by
    ext b
    cases b <;> simp
  have hu (p : PMF Bool) : p.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simp only [Set.indicator_univ, PMF.tsum_coe]
  simp only [hs, hu, tsub_self, PMF.toOuterMeasure_apply_singleton,
    fifths, PMF.ofFintype_apply, ite_true, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ← ENNReal.coe_sub, ← ENNReal.coe_add]
  change ((0 : ℝ≥0) : ℝ≥0∞) ≠ ↑((3 / 5 - 2 / 5) + (2 / 5 - 3 / 5) : ℝ≥0)
  exact ENNReal.coe_ne_coe.mpr (by
    norm_num [← NNReal.coe_inj, NNReal.coe_sub_def])

private noncomputable def xorJoint (d : Bool) : PMF (Bool × Bool) :=
  (uniformOfFintype Bool).bind fun a =>
    (PMF.pure (Bool.xor a d)).bind fun b => PMF.pure (a, b)

private theorem xor_marginals :
    IsApproxDP (fun d => (xorJoint d).map Prod.fst) (fun _ _ => True) 0 0 ∧
    IsApproxDP (fun d => (xorJoint d).map Prod.snd) (fun _ _ => True) 0 0 := by
  have hf (d : Bool) : (xorJoint d).map Prod.fst = uniformOfFintype Bool := by
    simp only [xorJoint, PMF.pure_bind, PMF.map_bind,
      PMF.pure_map, PMF.bind_pure]
  have hs (d : Bool) : (xorJoint d).map Prod.snd = uniformOfFintype Bool := by
    ext b
    cases d <;> cases b <;>
      norm_num [xorJoint, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
        PMF.bind_apply, tsum_fintype, uniformOfFintype_apply, PMF.pure_apply]
  constructor <;> apply isApproxDP_zero_iff.mpr
  · simpa only [hf] using
      isDP_const (uniformOfFintype Bool) (fun _ _ : Bool => True)
  · simpa only [hs] using
      isDP_const (uniformOfFintype Bool) (fun _ _ : Bool => True)

private theorem private_marginals_not_private_joint (ε : ℝ) :
    ¬IsApproxDP xorJoint (fun _ _ => True) ε 0 := by
  intro h
  have bad := (isApproxDP_zero_iff.mp h).2 false true trivial (false, false)
  simp only [xorJoint, bind_pair_apply, uniformOfFintype_apply,
    Fintype.card_bool, PMF.pure_apply, Bool.false_xor,
    ite_true, Bool.false_eq_true, ite_false, mul_zero, mul_one] at bad
  norm_num at bad

private theorem database_dependent_postprocessor_refuted (ε : ℝ) :
    IsApproxDP (fun _ : Bool => uniformOfFintype Bool) (fun _ _ => True) 0 0 ∧
    IsApproxDP (fun _ : Bool => (uniformOfFintype Bool).bind
      (fun _ => PMF.pure false)) (fun _ _ => True) 0 0 ∧
    ¬IsApproxDP (fun d : Bool => (uniformOfFintype Bool).bind
      (fun _ => PMF.pure d)) (fun _ _ => True) ε 0 := by
  have hp : IsApproxDP (fun _ : Bool => uniformOfFintype Bool)
      (fun _ _ => True) 0 0 := isApproxDP_zero_iff.mpr (isDP_const _ _)
  refine ⟨hp, isApproxDP_bind hp _, ?_⟩
  intro h
  have bad := (isApproxDP_zero_iff.mp h).2 false true trivial false
  norm_num [PMF.bind_const, PMF.pure_apply] at bad

end CSLibExtTest.Privacy.ApproximateDifferentialPrivacy
