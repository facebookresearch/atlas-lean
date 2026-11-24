/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.VersionSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# PAC learning: the Occam bound for consistent learners over a finite class

In Valiant's model of learning from examples (L. G. Valiant, *A theory of the learnable*,
Comm. ACM 27 (1984), 1134-1142), a learner sees `m` independent labelled examples and must output,
with probability at least `1 - δ`, a hypothesis whose error is at most `ε`. For a finite
hypothesis class `H` and a realizable distribution, consistency suffices (Blumer, Ehrenfeucht,
Haussler and Warmuth, *Occam's razor*, Inform. Process. Lett. 24 (1987), 377-380; Shalev-Shwartz
and Ben-David, *Understanding Machine Learning*, 2014, Section 2.3.1 and Corollary 2.3): a fixed
hypothesis of error above `ε` agrees with `m` independent examples with probability
`(1 - err)^m ≤ (1 - ε)^m ≤ exp (-ε m)`, and a union bound over `H` gives the result.

This file is stated in CSLib's PAC API (`Cslib.MachineLearning.PACLearning`): the 0-1 `error`
of a hypothesis under a joint distribution `D` on `X × Y`, labelled samples, `Learner`,
`VersionSpace`, `Realizable` and `IsConsistent`. It adds the SSBD form `trueError μ c h` of the
error against a target labelling, with the bridge `trueError_eq_error_map`, and the realizable
distribution family `realizableFamily C`. This is the *realizable* regime, with a rate
`log |H| / ε`; the agnostic bound through Hoeffding's inequality has rate `log |H| / ε²`.

Main results:

* `pi_consistent_eq`: a hypothesis agrees with `m` independent examples with probability exactly
  `(1 - err)^m`.
* `pi_exists_bad_consistent_le`: some hypothesis of the version space of `H` has error above `ε`
  with probability at most `|H| (1 - ε)^m`.
* `ae_realizable_of_error_eq_zero`: if some `h ∈ C` has error `0`, the sample is almost surely
  realizable by `C`.
* `pi_consistent_learner_error_gt_le`: **a consistent learner over a finite class has error above
  `ε` with probability at most `|H| (1 - ε)^m`** under every realizable distribution.
* `pi_consistent_learner_error_gt_le_of_log_div_le`: **Corollary 2.3 of Shalev-Shwartz and
  Ben-David**: if `m ≥ log (|H| / δ) / ε`, that probability is at most `δ`.
* `isPACLearnable_of_isConsistent`, `isPACLearnable_of_finite`: a nonempty finite class is
  `IsPACLearnable` over its realizable family (Corollary 3.2 of Shalev-Shwartz and Ben-David).

## Cost model

None: these are statements about sample sizes, not running times.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ### Error against a target labelling, and realizable distributions -/

/-- **True error against a target labelling.** For a distribution `μ` on instances, a target
labelling `c : X → Y` and a hypothesis `h : X → Y`, the true error of `h` is
`μ {x | h x ≠ c x}`, the probability that `h` disagrees with the target on a fresh instance
(Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, 2014, equation (2.1), where it
is written `L_{(D, f)}(h)`). It is CSLib's `error` under the pushforward of `μ` along the graph of
`c` (`trueError_eq_error_map`). -/
noncomputable def trueError (μ : Measure X) (c h : X → Y) : ℝ≥0∞ :=
  μ {x | h x ≠ c x}

/-- **Bridge to CSLib's error.** If the target `c` is measurable and the disagreement set
`{(x, y) | h x ≠ y}` is measurable, the true error of `h` against `c` under `μ` is CSLib's 0-1
`error` of `h` under the joint distribution `μ.map (x ↦ (x, c x))`. -/
theorem trueError_eq_error_map (μ : Measure X) {c : X → Y} (hc : Measurable c) (h : X → Y)
    (hmeas : MeasurableSet {p : X × Y | h p.1 ≠ p.2}) :
    trueError μ c h = error (μ.map fun x => (x, c x)) h := by
  have hφ : Measurable fun x => (x, c x) := measurable_id.prodMk hc
  rw [error, Measure.map_apply hφ hmeas, trueError]
  rfl

/-- **The realizable distribution family.** The joint distributions on `X × Y` under which some
concept of `C` has error `0`. Under such a distribution the optimal error of `C` is `0`, so CSLib's
`IsPACLearnable C (realizableFamily C)` is PAC learnability in the realizable case
(Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, 2014, Definition 2.1, the
realizability assumption, and Definition 3.1). -/
def realizableFamily (C : ConceptClass X Y) : Set (Measure (X × Y)) :=
  {D | ∃ h ∈ C, error D h = 0}

/-- **Labelling a distribution by a target gives a realizable distribution.** If `c` is
measurable and some `h ∈ C` with a measurable disagreement set has true error `0` against `c`
under `μ` (the realizability assumption of Shalev-Shwartz and Ben-David, Definition 2.1), then
`μ.map (x ↦ (x, c x))` belongs to the realizable family of `C`. -/
theorem map_graph_mem_realizableFamily (μ : Measure X) {C : ConceptClass X Y} {c : X → Y}
    (hc : Measurable c) {h : X → Y} (hC : h ∈ C)
    (hmeas : MeasurableSet {p : X × Y | h p.1 ≠ p.2}) (h0 : trueError μ c h = 0) :
    μ.map (fun x => (x, c x)) ∈ realizableFamily C :=
  ⟨h, hC, by rw [← trueError_eq_error_map μ hc h hmeas, h0]⟩

/-- On the realizable family, the optimal error of the class is `0`. -/
theorem optimalError_eq_zero_of_mem_realizableFamily {C : ConceptClass X Y}
    {D : Measure (X × Y)} (hD : D ∈ realizableFamily C) : optimalError D C = 0 := by
  obtain ⟨h, hC, h0⟩ := hD
  exact le_antisymm ((iInf₂_le h hC).trans h0.le) bot_le

/-! ### One hypothesis -/

/-- **A hypothesis survives `m` independent examples with probability `(1 - err)^m`.** Let `D` be
a probability distribution on labelled examples and `h` a hypothesis whose disagreement set is
measurable. Under the product distribution `D^m` of `m` independent examples, the probability
that `h` agrees with all of them is `(1 - error D h)^m` (Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, equation (2.8) and the line after it). -/
theorem pi_consistent_eq (D : Measure (X × Y)) [IsProbabilityMeasure D] (h : X → Y)
    (hmeas : MeasurableSet {p : X × Y | h p.1 ≠ p.2}) (m : ℕ) :
    Measure.pi (fun _ : Fin m => D) {S : LabeledSample X Y m | ∀ i, h (S i).1 = (S i).2} =
      (1 - error D h) ^ m := by
  have hset : {S : LabeledSample X Y m | ∀ i, h (S i).1 = (S i).2} =
      Set.pi univ (fun _ => {p : X × Y | h p.1 ≠ p.2}ᶜ) := by
    ext S; simp
  rw [hset, Measure.pi_pi, prob_compl_eq_one_sub hmeas, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, error]

/-- **A bad hypothesis survives `m` examples with probability at most `(1 - ε)^m`.** If the error
of `h` is at least `ε`, the probability under `D^m` that `h` agrees with `m` independent examples
is at most `(1 - ε)^m` (Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, 2014,
equation (2.9)). -/
theorem pi_consistent_le (D : Measure (X × Y)) [IsProbabilityMeasure D] (h : X → Y)
    (hmeas : MeasurableSet {p : X × Y | h p.1 ≠ p.2}) (m : ℕ) {ε : ℝ≥0∞}
    (hε : ε ≤ error D h) :
    Measure.pi (fun _ : Fin m => D) {S : LabeledSample X Y m | ∀ i, h (S i).1 = (S i).2} ≤
      (1 - ε) ^ m := by
  rw [pi_consistent_eq D h hmeas m]
  exact pow_le_pow_left₀ zero_le (tsub_le_tsub_left hε 1) m

/-! ### Union bound over a finite class -/

/-- **Union bound over a finite class (the Occam bound).** Let `H` be a finite set of hypotheses
with measurable disagreement sets. Under `D^m`, the probability that the version space of `H` at
the sample contains a hypothesis of error greater than `ε` is at most `|H| (1 - ε)^m`
(Blumer, Ehrenfeucht, Haussler and Warmuth, *Occam's razor*, Inform. Process. Lett. 24 (1987),
377-380; Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, 2014, equations
(2.5)-(2.9) and the display after them). -/
theorem pi_exists_bad_consistent_le (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Finset (X → Y)) (hmeas : ∀ h ∈ H, MeasurableSet {p : X × Y | h p.1 ≠ p.2}) (m : ℕ)
    (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ h ∈ VersionSpace (H : ConceptClass X Y) S, ε < error D h} ≤
      H.card * (1 - ε) ^ m := by
  classical
  set B := H.filter (fun h => ε < error D h)
  have hsub : {S : LabeledSample X Y m | ∃ h ∈ VersionSpace (H : ConceptClass X Y) S,
      ε < error D h} ⊆ ⋃ h ∈ B, {S | ∀ i, h (S i).1 = (S i).2} := by
    rintro S ⟨h, ⟨hH, hcons⟩, hbad⟩
    exact Set.mem_biUnion (Finset.mem_filter.2 ⟨hH, hbad⟩) hcons
  calc Measure.pi (fun _ : Fin m => D)
        {S | ∃ h ∈ VersionSpace (H : ConceptClass X Y) S, ε < error D h}
      ≤ Measure.pi (fun _ : Fin m => D) (⋃ h ∈ B, {S | ∀ i, h (S i).1 = (S i).2}) :=
        measure_mono hsub
    _ ≤ ∑ h ∈ B, Measure.pi (fun _ : Fin m => D) {S | ∀ i, h (S i).1 = (S i).2} :=
        measure_biUnion_finset_le B _
    _ ≤ ∑ _h ∈ B, (1 - ε) ^ m := by
        refine Finset.sum_le_sum fun h hB => ?_
        obtain ⟨hH, hbad⟩ := Finset.mem_filter.1 hB
        exact pi_consistent_le D h (hmeas h hH) m hbad.le
    _ = B.card * (1 - ε) ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ H.card * (1 - ε) ^ m :=
        mul_le_mul_left (Nat.cast_le.2 (Finset.card_filter_le H _)) _

/-- **The estimate `(1 - ε)^m ≤ exp (-ε m)`.** For real `ε ≥ 0` and every `m`,
`(1 - ε)^m ≤ exp (-ε m)` in `ℝ≥0∞` (truncated subtraction), from `1 - ε ≤ exp (-ε)`
(Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, 2014, the inequality used for
equation (2.9)). -/
theorem one_sub_ofReal_pow_le_ofReal_exp {ε : ℝ} (hε0 : 0 ≤ ε) (m : ℕ) :
    (1 - ENNReal.ofReal ε) ^ m ≤ ENNReal.ofReal (Real.exp (-(ε * m))) := by
  rcases le_or_gt ε 1 with hε1 | hε1
  · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hε0, ← ENNReal.ofReal_pow (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 - ε) ^ m ≤ (Real.exp (-ε)) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) m
      _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
  · have h0 : (1 : ℝ≥0∞) - ENNReal.ofReal ε = 0 := by
      rw [tsub_eq_zero_iff_le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hε1.le
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [h0, zero_pow hm.ne']; exact bot_le

/-- **The Occam bound in exponential form.** For real `ε ≥ 0`, the probability under `D^m` that
the version space of the finite class `H` at the sample contains a hypothesis of error greater
than `ε` is at most `|H| exp (-ε m)` (Shalev-Shwartz and Ben-David, *Understanding Machine
Learning*, 2014, the display before Corollary 2.3). -/
theorem pi_exists_bad_consistent_le_exp (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Finset (X → Y)) (hmeas : ∀ h ∈ H, MeasurableSet {p : X × Y | h p.1 ≠ p.2}) (m : ℕ)
    {ε : ℝ} (hε0 : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ h ∈ VersionSpace (H : ConceptClass X Y) S, ENNReal.ofReal ε < error D h} ≤
      ENNReal.ofReal (H.card * Real.exp (-(ε * m))) := by
  refine (pi_exists_bad_consistent_le D H hmeas m _).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  gcongr
  exact one_sub_ofReal_pow_le_ofReal_exp hε0 m

/-! ### Consistent learners under realizable distributions -/

/-- **Realizable distributions give realizable samples almost surely.** If some `h ∈ C` with a
measurable disagreement set has error `0` under `D`, then `m` independent examples from `D` are
almost surely realizable by `C` (Shalev-Shwartz and Ben-David, *Understanding Machine Learning*,
2014, Section 2.3.1, the note in Definition 2.1). -/
theorem ae_realizable_of_error_eq_zero (D : Measure (X × Y)) [IsProbabilityMeasure D]
    {C : ConceptClass X Y} {h : X → Y} (hC : h ∈ C)
    (hmeas : MeasurableSet {p : X × Y | h p.1 ≠ p.2}) (h0 : error D h = 0) (m : ℕ) :
    ∀ᵐ S ∂(Measure.pi (fun _ : Fin m => D)), Realizable C S := by
  have hG : MeasurableSet {S : LabeledSample X Y m | ∀ i, h (S i).1 = (S i).2} := by
    have : {S : LabeledSample X Y m | ∀ i, h (S i).1 = (S i).2} =
        Set.pi univ (fun _ => {p : X × Y | h p.1 ≠ p.2}ᶜ) := by ext S; simp
    rw [this]; exact MeasurableSet.univ_pi fun _ => hmeas.compl
  have hone := pi_consistent_eq D h hmeas m
  rw [h0, tsub_zero, one_pow] at hone
  have hnull : Measure.pi (fun _ : Fin m => D)
      {S : LabeledSample X Y m | ∀ i, h (S i).1 = (S i).2}ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hG, hone, tsub_self]
  refine measure_mono_null (fun S hS => ?_) hnull
  intro hcons
  exact hS ⟨h, hC, fun i => (hcons i).symm⟩

/-- **Consistent learners over a finite class are probably approximately correct.** Let `H` be a
finite set of hypotheses with measurable disagreement sets, `D` a probability distribution under
which some `h ∈ H` has error `0`, and `A` a learner consistent with `H` (CSLib's `IsConsistent`:
on every sample realizable by `H`, its output lies in the version space). Then the probability
under `D^m` that `A` outputs a hypothesis of error greater than `ε` is at most `|H| (1 - ε)^m`
(Blumer, Ehrenfeucht, Haussler and Warmuth, *Occam's razor*, Inform. Process. Lett. 24 (1987),
377-380; Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, 2014, Section 2.3.1). -/
theorem pi_consistent_learner_error_gt_le (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Finset (X → Y)) (hmeas : ∀ h ∈ H, MeasurableSet {p : X × Y | h p.1 ≠ p.2})
    (hreal : ∃ h ∈ H, error D h = 0) {m : ℕ} (A : Learner X Y m)
    (hA : IsConsistent A (H : ConceptClass X Y)) (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D) {S | ε < error D (A S)} ≤ H.card * (1 - ε) ^ m := by
  obtain ⟨h, hH, h0⟩ := hreal
  have hae := ae_realizable_of_error_eq_zero D (C := (H : ConceptClass X Y))
    (Finset.mem_coe.2 hH) (hmeas h hH) h0 m
  have hsub : {S : LabeledSample X Y m | ε < error D (A S)} ⊆
      {S | ¬ Realizable (H : ConceptClass X Y) S} ∪
        {S | ∃ h ∈ VersionSpace (H : ConceptClass X Y) S, ε < error D h} := by
    intro S hS
    by_cases hr : Realizable (H : ConceptClass X Y) S
    · exact Or.inr ⟨A S, hA S hr, hS⟩
    · exact Or.inl hr
  calc Measure.pi (fun _ : Fin m => D) {S | ε < error D (A S)}
      ≤ Measure.pi (fun _ : Fin m => D) {S | ¬ Realizable (H : ConceptClass X Y) S} +
          Measure.pi (fun _ : Fin m => D)
            {S | ∃ h ∈ VersionSpace (H : ConceptClass X Y) S, ε < error D h} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + H.card * (1 - ε) ^ m := by
        gcongr
        · exact (ae_iff.1 hae).le
        · exact pi_exists_bad_consistent_le D H hmeas m ε
    _ = H.card * (1 - ε) ^ m := zero_add _

/-- **Sample complexity of a finite class (Shalev-Shwartz and Ben-David, Corollary 2.3).** Let `H`
be a finite set of hypotheses with measurable disagreement sets, `D` a probability distribution
satisfying the realizability assumption (some `h ∈ H` has error `0`), `A` a learner consistent
with `H`, and let `0 < ε`, `0 < δ` and `m ≥ log (|H| / δ) / ε`. Then `A` outputs a hypothesis of
error greater than `ε` with probability at most `δ` under `D^m`: with probability at least
`1 - δ` its error is at most `ε` (Shalev-Shwartz and Ben-David, *Understanding Machine Learning*,
2014, Corollary 2.3, for consistent learners, which are the ERM rules of the realizable case).
-/
theorem pi_consistent_learner_error_gt_le_of_log_div_le (D : Measure (X × Y))
    [IsProbabilityMeasure D] (H : Finset (X → Y))
    (hmeas : ∀ h ∈ H, MeasurableSet {p : X × Y | h p.1 ≠ p.2})
    (hreal : ∃ h ∈ H, error D h = 0) {m : ℕ} (A : Learner X Y m)
    (hA : IsConsistent A (H : ConceptClass X Y)) {ε δ : ℝ} (hε0 : 0 < ε) (hδ : 0 < δ)
    (hm : Real.log (H.card / δ) / ε ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  refine (pi_consistent_learner_error_gt_le D H hmeas hreal A hA _).trans ?_
  have hcard : (0 : ℝ) < H.card := by
    obtain ⟨h, hH, -⟩ := hreal
    exact_mod_cast Finset.card_pos.2 ⟨h, hH⟩
  have hexp := one_sub_ofReal_pow_le_ofReal_exp hε0.le m
  calc (H.card : ℝ≥0∞) * (1 - ENNReal.ofReal ε) ^ m
      ≤ H.card * ENNReal.ofReal (Real.exp (-(ε * m))) := by gcongr
    _ = ENNReal.ofReal (H.card * Real.exp (-(ε * m))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hlog : Real.log (H.card / δ) ≤ ε * m := by
          rw [div_le_iff₀ hε0] at hm; linarith
        calc (H.card : ℝ) * Real.exp (-(ε * m))
            ≤ H.card * Real.exp (-Real.log (H.card / δ)) := by gcongr
          _ = δ := by
              rw [Real.exp_neg, Real.exp_log (by positivity)]
              field_simp

/-! ### PAC learnability of finite classes -/

/-- **Consistent learners make a finite class PAC learnable.** If `H` is a finite set of
hypotheses with measurable disagreement sets and, for every sample size `m`, `A m` is a learner
consistent with `H`, then `H` is PAC learnable (CSLib's `IsPACLearnable`) over its realizable
family, with sample size `⌈log (|H| / δ) / ε⌉` (Shalev-Shwartz and Ben-David, *Understanding
Machine Learning*, 2014, Corollary 3.2). -/
theorem isPACLearnable_of_isConsistent (H : Finset (X → Y))
    (hmeas : ∀ h ∈ H, MeasurableSet {p : X × Y | h p.1 ≠ p.2})
    (A : (m : ℕ) → Learner X Y m) (hA : ∀ m, IsConsistent (A m) (H : ConceptClass X Y)) :
    IsPACLearnable (H : ConceptClass X Y) (realizableFamily (H : ConceptClass X Y)) := by
  intro ε δ
  refine ⟨⌈Real.log (H.card / (δ.val : ℝ)) / (ε.val : ℝ)⌉₊, A _, fun D _ hD => ?_⟩
  rw [optimalError_eq_zero_of_mem_realizableFamily hD, zero_add]
  obtain ⟨h, hH, h0⟩ := hD
  have key := pi_consistent_learner_error_gt_le_of_log_div_le D H hmeas ⟨h, hH, h0⟩
    (A _) (hA _) (ε := (ε.val : ℝ)) (δ := (δ.val : ℝ)) (by exact_mod_cast ε.2.1)
    (by exact_mod_cast δ.2.1) (Nat.le_ceil _)
  simpa only [ENNReal.ofReal_coe_nnreal] using key

omit [MeasurableSpace X] [MeasurableSpace Y] in
open Classical in
/-- **A consistent learner for a finite class.** On a sample realizable by `H`, output a concept
of `H` that agrees with the sample; otherwise output a fixed member of `H`. -/
noncomputable def consistentLearner (H : Finset (X → Y)) (hH : H.Nonempty) (m : ℕ) :
    Learner X Y m := fun S =>
  if hS : Realizable (H : ConceptClass X Y) S then hS.choose else hH.choose

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- **The learner `consistentLearner` is consistent.** It is consistent with `H` in the sense of
CSLib's `IsConsistent`. -/
theorem isConsistent_consistentLearner (H : Finset (X → Y)) (hH : H.Nonempty) (m : ℕ) :
    IsConsistent (consistentLearner H hH m) (H : ConceptClass X Y) := by
  intro S hS
  simp only [consistentLearner, hS, ↓reduceDIte]
  exact mem_versionSpace_of_realizable hS.choose_spec.1 S hS.choose_spec.2

/-- **Every nonempty finite class is PAC learnable (Shalev-Shwartz and Ben-David,
Corollary 3.2).** A nonempty finite set `H` of hypotheses with measurable disagreement sets is
PAC learnable (CSLib's `IsPACLearnable`) over its realizable family. -/
theorem isPACLearnable_of_finite (H : Finset (X → Y)) (hH : H.Nonempty)
    (hmeas : ∀ h ∈ H, MeasurableSet {p : X × Y | h p.1 ≠ p.2}) :
    IsPACLearnable (H : ConceptClass X Y) (realizableFamily (H : ConceptClass X Y)) :=
  isPACLearnable_of_isConsistent H hmeas (consistentLearner H hH)
    (isConsistent_consistentLearner H hH)

end Cslib.MachineLearning.PACLearning
