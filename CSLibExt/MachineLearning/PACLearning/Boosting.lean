/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Occam
public import CSLibExt.MachineLearning.PACLearning.WeakLearnability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Boosting: weak learnability implies PAC learnability

R. E. Schapire, *The strength of weak learnability*, Machine Learning 5 (1990), 197–227,
Theorem 1: a concept class is weakly learnable if and only if it is strongly learnable. This file
proves the sample-complexity form of the nontrivial direction in CSLib's vocabulary, for binary
labels in the realizable case, on a countable instance space with measurable singletons.

Main result:

* `IsWeakPACLearnable.isPACLearnable_realizableFamily`: a class that is weakly PAC learnable over
  its realizable distributions is PAC learnable over them. The trivial converse is
  `IsPACLearnable.toIsWeakPACLearnable`.

Schapire boosts a weak learner by recursive majorities of three over filtered distributions. Since
CSLib's learners are deterministic and only their sample sizes matter here, the proof below boosts
on the sample instead: a majority vote of outputs of the weak learner on sub-samples chosen by
multiplicative weights is correct on the whole sample, and a sample compression argument, in the
manner of Littlestone and Warmuth's compression schemes, bounds its error. Let `A` be an
`(ε₀, 1 / 2)`-PAC learner from `m` examples for the realizable distributions of `C`, `ε₀ < 1 / 2`.

1. On a sample `S` of size `N` realizable by `C`, every positive weighting of its points defines a
   realizable distribution, the weighted empirical distribution. Since `A` fails on it with
   probability at most `1 / 2 < 1`, some `m` points of `S` make `A` output a hypothesis whose
   errors on `S` carry at most an `ε₀` fraction of the weight.
2. Multiplying the weight of a point by `b = 1 / (2 ε₀)` when the chosen hypothesis errs on it and
   by `b⁻¹` otherwise multiplies the total weight by at most `ρ = 1 / 2 + 2 ε₀ (1 - ε₀) < 1` in
   each round. After `T` rounds, a point on which at least half of the chosen hypotheses err still
   has weight at least `1`, so if `N ρ ^ T < 1` the majority vote of the `T` hypotheses is correct
   on every point of `S`.
3. The majority vote is determined by the `T m` points of `S` fed to `A`. For a fixed choice of
   their indices, a hypothesis of error above `ε` built from them agrees with the at least
   `N - T m` other examples, which are independent of them, with probability at most
   `(1 - ε) ^ (N - T m)`. A union bound over the `N ^ (T m)` choices of indices bounds the failure
   probability by `N ^ (T m) (1 - ε) ^ (N - T m)`, which is at most `δ` for `N = T ^ 3` once `T`
   is large.

## Cost model

None: these are statements about sample sizes, not running times.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal

namespace IsWeakPACLearnable

/-! ### Boosting by multiplicative weights on a finite set of points -/

/-- One round of multiplicative weights: if the points `w` carry at most an `ε₀` fraction of the
weights `u`, multiplying the weight of the points of `w` by `b` and the others by `b⁻¹ ≤ b`
multiplies the total weight by at most `(1 - ε₀) b⁻¹ + ε₀ b`. -/
private theorem sum_ite_mul_le {ι : Type*} [Fintype ι] (w : ι → Prop) [DecidablePred w]
    (u : ι → ℝ) {ε₀ b : ℝ} (hbb : b⁻¹ ≤ b) (hu : ∑ i ∈ univ.filter w, u i ≤ ε₀ * ∑ i, u i) :
    ∑ i, (if w i then b else b⁻¹) * u i ≤ ((1 - ε₀) * b⁻¹ + ε₀ * b) * ∑ i, u i := by
  have hsplit : ∑ i, (if w i then b else b⁻¹) * u i =
      b * ∑ i ∈ univ.filter w, u i + b⁻¹ * ∑ i ∈ univ.filter (fun i => ¬ w i), u i := by
    simp only [ite_mul, Finset.sum_ite, Finset.mul_sum]
  have hcompl := Finset.sum_filter_add_sum_filter_not univ w u
  rw [hsplit, ← hcompl]
  rw [← hcompl] at hu
  nlinarith [mul_le_mul_of_nonneg_left hu (sub_nonneg.2 hbb)]

/-- **The potential bound of multiplicative weights.** If every positive weighting of the points
admits a hypothesis whose errors carry at most an `ε₀` fraction of the weight, then for every `T`
there are `T` hypotheses for which the potential `∑ᵢ ∏ₜ (b if hₜ errs at i, b⁻¹ otherwise)` is at
most `|ι| ((1 - ε₀) b⁻¹ + ε₀ b) ^ T`. -/
private theorem exists_potential_le {ι H : Type*} [Fintype ι] (wrong : H → ι → Prop)
    [∀ h i, Decidable (wrong h i)] {ε₀ b : ℝ} (hb : 0 < b) (hbb : b⁻¹ ≤ b)
    (hweak : ∀ u : ι → ℝ, (∀ i, 0 < u i) →
      ∃ h, ∑ i ∈ univ.filter (wrong h ·), u i ≤ ε₀ * ∑ i, u i)
    (hρ : 0 ≤ (1 - ε₀) * b⁻¹ + ε₀ * b) (T : ℕ) :
    ∃ hs : Fin T → H, ∑ i, ∏ t, (if wrong (hs t) i then b else b⁻¹) ≤
      Fintype.card ι * ((1 - ε₀) * b⁻¹ + ε₀ * b) ^ T := by
  induction T with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ T ih =>
    obtain ⟨hs, hΦ⟩ := ih
    set u : ι → ℝ := fun i => ∏ t, (if wrong (hs t) i then b else b⁻¹) with hu_def
    have hu : ∀ i, 0 < u i := fun i =>
      Finset.prod_pos fun t _ => by split_ifs <;> positivity
    obtain ⟨h, hh⟩ := hweak u hu
    refine ⟨Fin.cons h hs, ?_⟩
    have hstep : ∀ i, ∏ t, (if wrong ((Fin.cons h hs : Fin (T + 1) → H) t) i then b else b⁻¹) =
        (if wrong h i then b else b⁻¹) * u i := fun i => by
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hu_def]
    simp only [hstep]
    calc ∑ i, (if wrong h i then b else b⁻¹) * u i
        ≤ ((1 - ε₀) * b⁻¹ + ε₀ * b) * ∑ i, u i := sum_ite_mul_le (wrong h) u hbb hh
      _ ≤ ((1 - ε₀) * b⁻¹ + ε₀ * b) * (Fintype.card ι * ((1 - ε₀) * b⁻¹ + ε₀ * b) ^ T) :=
          mul_le_mul_of_nonneg_left hΦ hρ
      _ = Fintype.card ι * ((1 - ε₀) * b⁻¹ + ε₀ * b) ^ (T + 1) := by ring

/-- A product of `T` factors `b ≥ 1` or `b⁻¹` is at least `1` when at least half of the factors
are `b`. -/
private theorem one_le_prod_ite {T : ℕ} (w : Fin T → Prop) [DecidablePred w] {b : ℝ}
    (hb : 1 ≤ b) (hw : T ≤ 2 * (univ.filter w).card) :
    1 ≤ ∏ t, (if w t then b else b⁻¹) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin T))) w
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  set a := (univ.filter w).card
  set c := (univ.filter fun t => ¬ w t).card
  have hca : c ≤ a := by omega
  have hb0 : 0 < b := by linarith
  calc (1 : ℝ) ≤ b ^ (a - c) := one_le_pow₀ hb
    _ = b ^ (a - c) * (b ^ c * b⁻¹ ^ c) := by
        rw [← mul_pow, mul_inv_cancel₀ hb0.ne', one_pow, mul_one]
    _ = b ^ a * b⁻¹ ^ c := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hca]

/-- **Boosting by multiplicative weights.** Let `0 < ε₀ < 1 / 2` and suppose that every positive
weighting of the finitely many points `ι` admits a hypothesis whose errors carry at most an `ε₀`
fraction of the weight. If `|ι| ρ ^ T < 1` with `ρ = 1 / 2 + 2 ε₀ (1 - ε₀)`, there are `T`
hypotheses such that fewer than half of them err at each point. -/
private theorem exists_forall_two_mul_card_lt {ι H : Type*} [Fintype ι] (wrong : H → ι → Prop)
    [∀ h i, Decidable (wrong h i)] {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1 / 2)
    (hweak : ∀ u : ι → ℝ, (∀ i, 0 < u i) →
      ∃ h, ∑ i ∈ univ.filter (wrong h ·), u i ≤ ε₀ * ∑ i, u i)
    {T : ℕ} (hT : Fintype.card ι * (1 / 2 + 2 * ε₀ * (1 - ε₀)) ^ T < 1) :
    ∃ hs : Fin T → H, ∀ i, 2 * (univ.filter fun t => wrong (hs t) i).card < T := by
  set b : ℝ := (2 * ε₀)⁻¹ with hb_def
  have hb1 : 1 ≤ b := by
    rw [hb_def]; exact one_le_inv₀ (by positivity) |>.2 (by linarith)
  have hb0 : 0 < b := by linarith
  have hbinv : b⁻¹ = 2 * ε₀ := by rw [hb_def, inv_inv]
  have hbb : b⁻¹ ≤ b := by rw [hbinv]; linarith
  have hρ : (1 - ε₀) * b⁻¹ + ε₀ * b = 1 / 2 + 2 * ε₀ * (1 - ε₀) := by
    rw [hbinv, hb_def]; field_simp; ring
  obtain ⟨hs, hΦ⟩ := exists_potential_le wrong hb0 hbb hweak (by rw [hρ]; nlinarith) T
  rw [hρ] at hΦ
  refine ⟨hs, fun i => ?_⟩
  by_contra hi
  push Not at hi
  have hone : 1 ≤ ∏ t, (if wrong (hs t) i then b else b⁻¹) := one_le_prod_ite _ hb1 hi
  have hnonneg : ∀ j, 0 ≤ ∏ t, (if wrong (hs t) j then b else b⁻¹) := fun j =>
    Finset.prod_nonneg fun t _ => by split_ifs <;> positivity
  have := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  linarith

/-! ### Majority votes -/

/-- The majority vote of `T` binary hypotheses: `true` exactly when more than half of them say
`true`. -/
private def majorityVote {X : Type*} {T : ℕ} (hs : Fin T → X → Bool) (x : X) : Bool :=
  decide (T < 2 * (univ.filter fun t => hs t x = true).card)

/-- The majority vote predicts the label `y` at `x` when fewer than half of the hypotheses
disagree with `y` there. -/
private theorem majorityVote_eq {X : Type*} {T : ℕ} (hs : Fin T → X → Bool) (x : X) (y : Bool)
    (h : 2 * (univ.filter fun t => hs t x ≠ y).card < T) : majorityVote hs x = y := by
  have hcard := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin T)))
    (fun t => hs t x ≠ y)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  simp only [not_not] at hcard
  unfold majorityVote
  cases y with
  | true =>
    simp only [ne_eq, Bool.not_eq_true] at h hcard
    simp only [decide_eq_true_eq]
    omega
  | false =>
    simp only [ne_eq, Bool.not_eq_false] at h hcard
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-! ### The weak learner on weighted samples -/

/-- The weighted empirical distribution of a sample `S` with weights `u`: the point `S i` has mass
`u i / ∑ⱼ u j`. -/
private noncomputable def weightedSample {X : Type*} [MeasurableSpace X] {N : ℕ}
    (S : LabeledSample X Bool N) (u : Fin N → ℝ) : Measure (X × Bool) :=
  ∑ i, ENNReal.ofReal (u i / ∑ j, u j) • Measure.dirac (S i)

/-- The weighted empirical distribution gives a set the total mass of the sample points in it. -/
private theorem weightedSample_apply {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {N : ℕ} (S : LabeledSample X Bool N) (u : Fin N → ℝ)
    (s : Set (X × Bool)) :
    weightedSample S u s =
      ∑ i, s.indicator (fun _ => ENNReal.ofReal (u i / ∑ j, u j)) (S i) := by
  simp only [weightedSample]
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hi : S i ∈ s <;> simp [hi]

/-- The error of a hypothesis under the weighted empirical distribution is the fraction of the
weight carried by the points where it errs. -/
private theorem error_weightedSample {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {N : ℕ} (S : LabeledSample X Bool N) {u : Fin N → ℝ}
    (hu : ∀ i, 0 < u i) (h : X → Bool) :
    error (weightedSample S u) h =
      ENNReal.ofReal ((∑ i ∈ univ.filter (fun i => h (S i).1 ≠ (S i).2), u i) / ∑ j, u j) := by
  rw [error, weightedSample_apply, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
    (fun i _ => div_nonneg (hu i).le (Finset.sum_nonneg fun j _ => (hu j).le)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator_apply]

/-- With positive weights on a nonempty sample, the weighted empirical distribution is a
probability measure. -/
private theorem isProbabilityMeasure_weightedSample {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {N : ℕ} (S : LabeledSample X Bool N) {u : Fin N → ℝ}
    (hu : ∀ i, 0 < u i) (hN : 0 < N) : IsProbabilityMeasure (weightedSample S u) := by
  constructor
  have hU : 0 < ∑ j, u j := Finset.sum_pos (fun i _ => hu i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  rw [weightedSample_apply]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hu i).le hU.le), ← Finset.sum_div,
    div_self hU.ne', ENNReal.ofReal_one]

/-- **The weak learner on a weighted sample.** Let `A` be an `(ε₀, δ₀)`-PAC learner with `m`
examples for the realizable distributions of `C`. On a nonempty sample `S` realizable by `C`, every
positive weighting `u` of its points admits indices `ι` such that the output of `A` on the points
`S ∘ ι` errs on points carrying at most an `ε₀` fraction of the weight. -/
private theorem exists_index_weighted_error_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {C : ConceptClass X Bool} {m : ℕ}
    {ε₀ δ₀ : Set.Ioo (0 : ℝ≥0) 1} {A : Learner X Bool m}
    (hA : ∀ (D : Measure (X × Bool)) [IsProbabilityMeasure D], D ∈ realizableFamily C →
      Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ↑ε₀.val < error D (A S)} ≤
        ↑δ₀.val)
    {N : ℕ} (hN : 0 < N) {S : LabeledSample X Bool N} (hS : Realizable C S) (u : Fin N → ℝ)
    (hu : ∀ i, 0 < u i) :
    ∃ ι : Fin m → Fin N,
      ∑ i ∈ univ.filter (fun i => A (S ∘ ι) (S i).1 ≠ (S i).2), u i ≤ ε₀.val * ∑ i, u i := by
  have := isProbabilityMeasure_weightedSample S hu hN
  have hU : 0 < ∑ j, u j := Finset.sum_pos (fun i _ => hu i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hPreal : weightedSample S u ∈ realizableFamily C := by
    obtain ⟨c, hc, hcS⟩ := hS
    refine ⟨c, hc, ?_⟩
    rw [error_weightedSample S hu]
    have : univ.filter (fun i => c (S i).1 ≠ (S i).2) = ∅ := by
      ext i; simp [hcS i]
    simp [this]
  have hbad := hA (weightedSample S u) hPreal
  rw [optimalError_eq_zero_of_mem_realizableFamily hPreal, zero_add] at hbad
  set G : Set (Fin m → X × Bool) := {S' | ∀ j, S' j ∈ Set.range S} with hG_def
  have hG : Measure.pi (fun _ : Fin m => weightedSample S u) Gᶜ = 0 := by
    have hrange : weightedSample S u (Set.range S)ᶜ = 0 := by
      rw [weightedSample_apply]
      simp
    have : Gᶜ = ⋃ j, Function.eval j ⁻¹' (Set.range S)ᶜ := by
      ext S'; simp [hG_def]
    rw [this]
    exact measure_iUnion_null fun j => Measure.pi_eval_preimage_null _ hrange
  have hne : ({S' | ↑ε₀.val < error (weightedSample S u) (A S')}ᶜ ∩ G).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsub : {S' : Fin m → X × Bool | ↑ε₀.val < error (weightedSample S u) (A S')}ᶜ ⊆ Gᶜ :=
      fun S' h1 h2 => (Set.eq_empty_iff_forall_notMem.1 hemp) S' ⟨h1, h2⟩
    have h0 := measure_mono_null hsub hG
    rw [prob_compl_eq_zero_iff MeasurableSet.of_discrete] at h0
    rw [h0] at hbad
    exact absurd (ENNReal.one_le_coe_iff.1 hbad) (not_le.2 δ₀.2.2)
  obtain ⟨S', hS'bad, hS'G⟩ := hne
  choose ι hι using hS'G
  have hSι : S ∘ ι = S' := funext hι
  refine ⟨ι, ?_⟩
  have herr : error (weightedSample S u) (A (S ∘ ι)) ≤ ↑ε₀.val := by
    rw [hSι]; exact not_lt.1 hS'bad
  rw [error_weightedSample S hu, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_le_ofReal_iff (by positivity), div_le_iff₀ hU] at herr
  exact herr

/-! ### Sample compression -/

/-- A hypothesis agrees with `|I|` independent examples with probability `(1 - err)^|I|`, for any
finite index type `I`. -/
private theorem pi_consistent_eq_of_fintype {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {I : Type*} [Fintype I] (D : Measure (α × β)) [IsProbabilityMeasure D]
    (h : α → β) (hmeas : MeasurableSet {p : α × β | h p.1 ≠ p.2}) :
    Measure.pi (fun _ : I => D) {b : I → α × β | ∀ i, h (b i).1 = (b i).2} =
      (1 - error D h) ^ Fintype.card I := by
  have hset : {b : I → α × β | ∀ i, h (b i).1 = (b i).2} =
      Set.pi univ (fun _ => {p : α × β | h p.1 ≠ p.2}ᶜ) := by
    ext b; simp
  rw [hset, Measure.pi_pi, prob_compl_eq_one_sub hmeas, Finset.prod_const, Finset.card_univ,
    error]

/-- A hypothesis computed from the examples indexed by `p` is consistent with the other
examples and has error above `ε` with probability at most `(1 - ε)` to the number of the other
examples. -/
private theorem pi_restrict_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (D : Measure (X × Bool)) [IsProbabilityMeasure D] {ι : Type*}
    [Fintype ι] (p : ι → Prop) [DecidablePred p] (g : (Subtype p → X × Bool) → X → Bool)
    (ε : ℝ≥0∞) :
    Measure.pi (fun _ : ι => D)
        {S | (∀ i, g (fun j => S j) (S i).1 = (S i).2) ∧ ε < error D (g fun j => S j)} ≤
      (1 - ε) ^ Fintype.card {i // ¬ p i} := by
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => D) p
  set F : Set ((Subtype p → X × Bool) × ({i // ¬ p i} → X × Bool)) :=
    {ab | ε < error D (g ab.1) ∧ ∀ i, g ab.1 (ab.2 i).1 = (ab.2 i).2} with hF
  have hsub : {S : ι → X × Bool | (∀ i, g (fun j => S j) (S i).1 = (S i).2) ∧
      ε < error D (g fun j => S j)} ⊆
        MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X × Bool) p ⁻¹' F := by
    rintro S ⟨hcons, herr⟩
    exact ⟨herr, fun i => hcons i⟩
  have hFmeas : MeasurableSet F := MeasurableSet.of_discrete
  have hslice : ∀ a, (Measure.pi fun _ : {i // ¬ p i} => D) (Prod.mk a ⁻¹' F) ≤
      (1 - ε) ^ Fintype.card {i // ¬ p i} := by
    intro a
    by_cases ha : ε < error D (g a)
    · have : Prod.mk a ⁻¹' F = {b | ∀ i, g a (b i).1 = (b i).2} := by
        ext b; simp [hF, ha]
      rw [this, pi_consistent_eq_of_fintype D (g a) MeasurableSet.of_discrete]
      exact pow_le_pow_left₀ zero_le (tsub_le_tsub_left ha.le 1) _
    · have : Prod.mk a ⁻¹' F = ∅ := by
        ext b; simp [hF, ha]
      rw [this, measure_empty]
      exact zero_le
  calc Measure.pi (fun _ : ι => D)
        {S | (∀ i, g (fun j => S j) (S i).1 = (S i).2) ∧ ε < error D (g fun j => S j)}
      ≤ Measure.pi (fun _ : ι => D)
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X × Bool) p ⁻¹' F) :=
        measure_mono hsub
    _ = ((Measure.pi fun _ : Subtype p => D).prod (Measure.pi fun _ : {i // ¬ p i} => D)) F :=
        hmp.measure_preimage hFmeas.nullMeasurableSet
    _ = ∫⁻ a, (Measure.pi fun _ : {i // ¬ p i} => D) (Prod.mk a ⁻¹' F)
          ∂(Measure.pi fun _ : Subtype p => D) := Measure.prod_apply hFmeas
    _ ≤ ∫⁻ _a, (1 - ε) ^ Fintype.card {i // ¬ p i} ∂(Measure.pi fun _ : Subtype p => D) :=
        lintegral_mono hslice
    _ = (1 - ε) ^ Fintype.card {i // ¬ p i} := by simp

/-- **The sample compression bound.** For a fixed map `κ` from `J` to the indices of a sample of
size `N`, a hypothesis reconstructed from the examples `S ∘ κ` is consistent with the whole sample
and has error above `ε` with probability at most `(1 - ε) ^ (N - |J|)`. -/
private theorem pi_compress_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (D : Measure (X × Bool)) [IsProbabilityMeasure D] {N : ℕ}
    {J : Type*} [Fintype J] (κ : J → Fin N) (R : (J → X × Bool) → X → Bool) (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin N => D)
        {S | (∀ i, R (S ∘ κ) (S i).1 = (S i).2) ∧ ε < error D (R (S ∘ κ))} ≤
      (1 - ε) ^ (N - Fintype.card J) := by
  have key := pi_restrict_le D (fun i => i ∈ Finset.univ.image κ)
    (fun a => R fun j => a ⟨κ j, Finset.mem_image_of_mem κ (Finset.mem_univ j)⟩) ε
  refine (le_of_eq_of_le rfl key).trans (pow_le_pow_right_of_le_one' tsub_le_self ?_)
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]
  refine Nat.sub_le_sub_left ?_ N
  calc (Finset.univ.filter fun i => i ∈ Finset.univ.image κ).card
      ≤ (Finset.univ.image κ).card :=
        Finset.card_le_card fun i hi => (Finset.mem_filter.1 hi).2
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card J := Finset.card_univ

/-! ### The boosted learner -/

open Classical in
/-- The boosted learner on samples of size `N`: it looks for `T` index maps `κ t : Fin m → Fin N`
such that the majority vote of the outputs of the weak learner `A` on the sub-samples `S ∘ κ t`
is consistent with the sample, and outputs that majority vote (a constant if there is none). -/
private noncomputable def boostedLearner {X : Type*} {m : ℕ} (A : Learner X Bool m)
    (T N : ℕ) : Learner X Bool N := fun S =>
  if h : ∃ κ : Fin T → Fin m → Fin N,
      ∀ i, majorityVote (fun t => A (S ∘ κ t)) (S i).1 = (S i).2
  then majorityVote fun t => A (S ∘ h.choose t)
  else fun _ => false

/-- **The failure probability of the boosted learner.** If `A` is an `(ε₀, δ₀)`-PAC learner with
`m` examples for the realizable distributions of `C`, with `ε₀ < 1 / 2`, and `N ρ ^ T < 1` for
`ρ = 1 / 2 + 2 ε₀ (1 - ε₀)`, the boosted learner errs by more than `ε` with probability at most
`N ^ (T m) (1 - ε) ^ (N - T m)` under every realizable distribution. -/
private theorem pi_boostedLearner_error_gt_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {C : ConceptClass X Bool} {m : ℕ}
    {ε₀ δ₀ : Set.Ioo (0 : ℝ≥0) 1} (hε₀ : ε₀.val < 1 / 2) {A : Learner X Bool m}
    (hA : ∀ (D : Measure (X × Bool)) [IsProbabilityMeasure D], D ∈ realizableFamily C →
      Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ↑ε₀.val < error D (A S)} ≤
        ↑δ₀.val)
    {T N : ℕ} (hN : 0 < N)
    (hT : (N : ℝ) * (1 / 2 + 2 * (ε₀.val : ℝ) * (1 - ε₀.val)) ^ T < 1)
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] (hD : D ∈ realizableFamily C)
    (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin N => D) {S | ε < error D (boostedLearner A T N S)} ≤
      ((N ^ m) ^ T : ℕ) * (1 - ε) ^ (N - T * m) := by
  -- the reconstruction of the majority vote from the `T m` compressed examples
  let R : (Fin T × Fin m → X × Bool) → X → Bool :=
    fun a => majorityVote fun t => A fun j => a (t, j)
  let E : (Fin T → Fin m → Fin N) → Set (LabeledSample X Bool N) := fun κ =>
    {S | (∀ i, R (S ∘ fun q => κ q.1 q.2) (S i).1 = (S i).2) ∧
      ε < error D (R (S ∘ fun q => κ q.1 q.2))}
  obtain ⟨c, hc, hc0⟩ := hD
  have hreal := ae_realizable_of_error_eq_zero D hc MeasurableSet.of_discrete hc0 N
  have hsub : {S : LabeledSample X Bool N | ε < error D (boostedLearner A T N S)} ⊆
      {S | ¬ Realizable C S} ∪ ⋃ κ, E κ := by
    intro S hS
    by_cases hSr : Realizable C S
    · right
      have hweak : ∀ u : Fin N → ℝ, (∀ i, 0 < u i) → ∃ ι : Fin m → Fin N,
          ∑ i ∈ univ.filter (fun i => A (S ∘ ι) (S i).1 ≠ (S i).2), u i ≤
            (ε₀.val : ℝ) * ∑ i, u i :=
        fun u hu => exists_index_weighted_error_le hA hN hSr u hu
      obtain ⟨hs, hhs⟩ := exists_forall_two_mul_card_lt
        (fun (ι : Fin m → Fin N) i => A (S ∘ ι) (S i).1 ≠ (S i).2) ε₀.2.1
        (by exact_mod_cast hε₀) hweak (by rwa [Fintype.card_fin])
      have hex : ∃ κ : Fin T → Fin m → Fin N,
          ∀ i, majorityVote (fun t => A (S ∘ κ t)) (S i).1 = (S i).2 :=
        ⟨hs, fun i => majorityVote_eq _ _ _ (hhs i)⟩
      have hB : boostedLearner A T N S = majorityVote fun t => A (S ∘ hex.choose t) :=
        dite_eq_left hex
      have hS' : ε < error D (boostedLearner A T N S) := hS
      rw [hB] at hS'
      exact Set.mem_iUnion.2 ⟨hex.choose, fun i => hex.choose_spec i, hS'⟩
    · exact Or.inl hSr
  calc Measure.pi (fun _ : Fin N => D) {S | ε < error D (boostedLearner A T N S)}
      ≤ Measure.pi (fun _ : Fin N => D) ({S | ¬ Realizable C S} ∪ ⋃ κ, E κ) :=
        measure_mono hsub
    _ ≤ Measure.pi (fun _ : Fin N => D) {S | ¬ Realizable C S} +
          ∑ κ, Measure.pi (fun _ : Fin N => D) (E κ) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ 0 + ∑ _κ : Fin T → Fin m → Fin N, (1 - ε) ^ (N - T * m) := by
        gcongr with κ
        · exact (ae_iff.1 hreal).le
        · have := pi_compress_le D (fun q : Fin T × Fin m => κ q.1 q.2) R ε
          rwa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    _ = ((N ^ m) ^ T : ℕ) * (1 - ε) ^ (N - T * m) := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [Fintype.card_fin]

/-- The numerical estimate: if `1 ≤ T` and `4 m - log δ ≤ ε T`, then
`(T³)^(m T) exp (-ε (T³ - T m)) ≤ δ`. -/
private theorem pow_mul_exp_le {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {m T : ℕ} (hT : 1 ≤ T) (hTε : 4 * m - Real.log δ ≤ ε * T) :
    (((T ^ 3) ^ m) ^ T : ℕ) * Real.exp (-(ε * ((T ^ 3 - T * m : ℕ) : ℝ))) ≤ δ := by
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have ht1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hmT : (m : ℝ) ≤ T := by nlinarith
  have hmT2 : T * m ≤ T ^ 3 := by
    have : m ≤ T := by exact_mod_cast hmT
    calc T * m ≤ T * T := Nat.mul_le_mul_left T this
      _ ≤ T * T * T := Nat.le_mul_of_pos_right _ (by omega)
      _ = T ^ 3 := by ring
  rw [Nat.cast_sub hmT2]
  push_cast
  set t : ℝ := (T : ℝ) with ht_def
  have hpow : ((t ^ 3) ^ m) ^ T ≤ Real.exp (3 * m * t ^ 2) := by
    have ht : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    calc ((t ^ 3) ^ m) ^ T ≤ ((Real.exp t ^ 3) ^ m) ^ T := by gcongr
      _ = Real.exp (3 * m * t ^ 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1
          simp only [t]
          push_cast
          ring
  calc ((t ^ 3) ^ m) ^ T * Real.exp (-(ε * (t ^ 3 - t * m)))
      ≤ Real.exp (3 * m * t ^ 2) * Real.exp (-(ε * (t ^ 3 - t * m))) := by gcongr
    _ = Real.exp (3 * m * t ^ 2 - ε * (t ^ 3 - t * m)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (Real.log δ) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : (4 * m - Real.log δ) * t ^ 2 ≤ ε * t * t ^ 2 :=
          mul_le_mul_of_nonneg_right hTε (by positivity)
        have h2 : -Real.log δ ≤ -Real.log δ * t ^ 2 := by
          have : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
          nlinarith
        have h3 : ε * t * m ≤ t ^ 2 * m := by
          have : ε * t ≤ t ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg m)
        nlinarith
    _ = δ := Real.exp_log hδ

end IsWeakPACLearnable

/-- **Weak learnability implies PAC learnability** (the sample-complexity form of Schapire's
Theorem 1, *The strength of weak learnability*, Machine Learning 5, 1990, whose proof boosts a weak
learner by majority votes over filtered distributions): on a countable instance space with
measurable singletons, a class `C` of binary hypotheses that is weakly PAC learnable over its
realizable distributions is PAC learnable over them. -/
theorem IsWeakPACLearnable.isPACLearnable_realizableFamily {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {C : ConceptClass X Bool}
    (h : IsWeakPACLearnable C (realizableFamily C)) : IsPACLearnable C (realizableFamily C) := by
  obtain ⟨ε₀, hε₀, hweak⟩ := h
  obtain ⟨m, A, hA⟩ := hweak ⟨1 / 2, by norm_num, by norm_num⟩
  intro ε δ
  have he₀ : (0 : ℝ) < ε₀.val := by exact_mod_cast ε₀.2.1
  have he₀' : (ε₀.val : ℝ) < 1 / 2 := by exact_mod_cast hε₀
  set ρ : ℝ := 1 / 2 + 2 * (ε₀.val : ℝ) * (1 - ε₀.val) with hρ_def
  have hρ0 : 0 < ρ := by nlinarith
  have hρ1 : ρ < 1 := by nlinarith
  have hε : (0 : ℝ) < ε.val := by exact_mod_cast ε.2.1
  have hε1 : (ε.val : ℝ) < 1 := by exact_mod_cast ε.2.2
  have hδ : (0 : ℝ) < δ.val := by exact_mod_cast δ.2.1
  have hδ1 : (δ.val : ℝ) < 1 := by exact_mod_cast δ.2.2
  obtain ⟨T, hT1, hTρ, hTε⟩ : ∃ T : ℕ, 1 ≤ T ∧ (T : ℝ) ^ 3 * ρ ^ T < 1 ∧
      4 * m - Real.log δ.val ≤ ε.val * T := by
    have h1 := eventually_ge_atTop 1
    have h2 := (tendsto_pow_const_div_const_pow_of_one_lt 3
      ((one_lt_inv₀ hρ0).2 hρ1)).eventually (gt_mem_nhds zero_lt_one)
    have h3 := tendsto_natCast_atTop_atTop.eventually_ge_atTop
      ((4 * m - Real.log δ.val) / ε.val)
    obtain ⟨T, hT1, hT2, hT3⟩ := (h1.and (h2.and h3)).exists
    refine ⟨T, hT1, ?_, ?_⟩
    · rwa [inv_pow, div_inv_eq_mul] at hT2
    · rw [div_le_iff₀ hε] at hT3
      linarith
  refine ⟨T ^ 3, boostedLearner A T (T ^ 3), fun D _ hD => ?_⟩
  rw [optimalError_eq_zero_of_mem_realizableFamily hD, zero_add]
  have hN : 0 < T ^ 3 := by positivity
  have hTN : ((T ^ 3 : ℕ) : ℝ) * ρ ^ T < 1 := by rwa [Nat.cast_pow]
  refine (pi_boostedLearner_error_gt_le hε₀ hA hN hTN D hD _).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal (p := ε.val), ← ENNReal.ofReal_coe_nnreal (p := δ.val)]
  calc (((T ^ 3) ^ m) ^ T : ℕ) * (1 - ENNReal.ofReal ε.val) ^ (T ^ 3 - T * m)
      ≤ (((T ^ 3) ^ m) ^ T : ℕ) *
          ENNReal.ofReal (Real.exp (-(ε.val * ((T ^ 3 - T * m : ℕ) : ℝ)))) := by
        gcongr
        exact one_sub_ofReal_pow_le_ofReal_exp hε.le _
    _ = ENNReal.ofReal ((((T ^ 3) ^ m) ^ T : ℕ) *
          Real.exp (-(ε.val * ((T ^ 3 - T * m : ℕ) : ℝ)))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ.val :=
        ENNReal.ofReal_le_ofReal (pow_mul_exp_le hε hε1 hδ hδ1 hT1 hTε)

end Cslib.MachineLearning.PACLearning
