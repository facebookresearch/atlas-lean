/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.PACLearning.FiniteClass

/-! Populated and boundary clients of the canonical finite-class PAC API. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning.FiniteClassTests

abbrev zeroConcept : Bool → Bool := fun _ => false

def twoConcepts : ConceptClass Bool Bool := {zeroConcept, id}

/-- Prefer the nonconstant hypothesis whenever it fits; otherwise use zero. -/
def learner (m : ℕ) : Learner Bool Bool m := fun S =>
  if ∀ i, (S i).1 = (S i).2 then id else zeroConcept

theorem learner_consistent (m : ℕ) : IsConsistent (learner m) twoConcepts := by
  intro S hS
  unfold learner
  split_ifs with hi
  · exact ⟨by simp [twoConcepts], hi⟩
  · obtain ⟨c, hc, hlabels⟩ := hS
    simp only [twoConcepts, mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨by simp [twoConcepts], fun i => (hlabels i).symm⟩
    · exact (hi (fun i => (hlabels i).symm)).elim

theorem twoConcepts_finite : twoConcepts.Finite := by
  exact (finite_singleton id).insert zeroConcept

theorem twoConcepts_nonempty : twoConcepts.Nonempty := by
  exact ⟨zeroConcept, by simp [twoConcepts]⟩

theorem twoConcepts_graphs (h : Bool → Bool) (_hh : h ∈ twoConcepts) :
    MeasurableSet {p : Bool × Bool | p.2 = h p.1} := by
  exact Set.toFinite _ |>.measurableSet

noncomputable def uniform : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true

instance : IsProbabilityMeasure uniform := by
  constructor
  norm_num [uniform, Measure.add_apply, Measure.smul_apply]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

noncomputable def quarter : Ioo (0 : ℝ≥0) 1 :=
  ⟨1 / 4, by constructor <;> norm_num⟩
noncomputable def half : Ioo (0 : ℝ≥0) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩

theorem uniform_error (h : Bool → Bool) :
    error (uniform.map (fun x => (x, false))) h =
      (1 / 2 : ℝ≥0∞) * (if h false ≠ false then 1 else 0) +
      (1 / 2 : ℝ≥0∞) * (if h true ≠ false then 1 else 0) := by
  have hφ : Measurable (fun x : Bool => (x, false)) :=
    measurable_id.prodMk measurable_const
  unfold error
  rw [Measure.map_apply hφ (Set.toFinite _ |>.measurableSet)]
  simp [uniform, Measure.add_apply, Measure.smul_apply, Set.indicator]

theorem nonconstant_risk :
    error (uniform.map (fun x => (x, false))) id = (1 / 2 : ℝ≥0∞) := by
  simp [uniform_error]

theorem target_risk_zero :
    error (uniform.map (fun x => (x, false))) zeroConcept = 0 := by
  simp [uniform_error]

theorem uniform_agreement :
    (uniform.map (fun x => (x, false)))
      {p : Bool × Bool | p.1 = p.2} = (1 / 2 : ℝ≥0∞) := by
  have hφ : Measurable (fun x : Bool => (x, false)) :=
    measurable_id.prodMk measurable_const
  rw [Measure.map_apply hφ (Set.toFinite _ |>.measurableSet)]
  simp [uniform, Measure.add_apply, Measure.smul_apply]

theorem failure_event (m : ℕ) :
    {S : LabeledSample Bool Bool m | (quarter.val : ℝ≥0∞) <
      error (uniform.map (fun x => (x, false))) (learner m S)} =
    univ.pi (fun _ : Fin m => {p : Bool × Bool | p.1 = p.2}) := by
  ext S
  by_cases hs : ∀ i : Fin m, (S i).1 = (S i).2
  · norm_num [learner, hs, nonconstant_risk, quarter, ENNReal.inv_lt_inv]
  · simp [learner, hs, target_risk_zero, quarter]

/-- This is an exact mass calculation, not an application of the upper bound. -/
theorem failure_mass (m : ℕ) :
    (Measure.pi (fun _ : Fin m => uniform.map (fun x => (x, false))))
      {S | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) (learner m S)} =
      (1 / 2 : ℝ≥0∞) ^ m := by
  rw [failure_event, Measure.pi_pi]
  simp [uniform_agreement]

theorem one_sample_positive_failure :
    (Measure.pi (fun _ : Fin 1 => uniform.map (fun x => (x, false))))
      {S | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) (learner 1 S)} =
      (1 / 2 : ℝ≥0∞) := by
  simp [failure_mass]

theorem no_samples_failure :
    (Measure.pi (fun _ : Fin 0 => uniform.map (fun x => (x, false))))
      {S | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) (learner 0 S)} = 1 := by
  simp [failure_mass]

theorem twoConcepts_card : twoConcepts.ncard = 2 := by
  have hne : zeroConcept ≠ (id : Bool → Bool) := by
    intro h
    have hh := congrFun h true
    simp at hh
  exact ncard_pair hne

theorem sixteen_meets_log_bound :
    (Real.log (twoConcepts.ncard : ℝ) +
      Real.log (1 / (quarter.val : ℝ))) / (quarter.val : ℝ) ≤ (16 : ℝ) := by
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  norm_num [twoConcepts_card, quarter] at *
  linarith

/-- Invoke the public logarithmic theorem with a concrete nonconstant class. -/
theorem sixteen_sample_guarantee :
    (Measure.pi (fun _ : Fin 16 => uniform.map (fun x => (x, false))))
      {S | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) (learner 16 S)} ≤
      (quarter.val : ℝ≥0∞) := by
  exact (learner_consistent 16).failure_le_of_log_bound
    twoConcepts_finite twoConcepts_nonempty twoConcepts_graphs
    quarter quarter sixteen_meets_log_bound uniform
    (by simp [twoConcepts]) measurable_const

theorem strict_threshold_equality (m : ℕ) :
    (Measure.pi (fun _ : Fin m => uniform.map (fun x => (x, false))))
      {S | (half.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) (learner m S)} = 0 := by
  have hempty : {S : LabeledSample Bool Bool m |
      (half.val : ℝ≥0∞) < error (uniform.map (fun x => (x, false)))
        (learner m S)} = ∅ := by
    ext S
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    unfold learner
    split_ifs <;> simp [nonconstant_risk, target_risk_zero, half]
  rw [hempty, measure_empty]

theorem zero_mass_disagreement :
    (Measure.dirac false : Measure Bool) {true} = 0 ∧
    id true ≠ zeroConcept true ∧
    error ((Measure.dirac false : Measure Bool).map
      (fun x => (x, false))) id = 0 := by
  constructor
  · simp
  constructor
  · decide
  · have hφ : Measurable (fun x : Bool => (x, false)) :=
      measurable_id.prodMk measurable_const
    unfold error
    rw [Measure.map_apply hφ (Set.toFinite _ |>.measurableSet)]
    simp

theorem singleton_consistent (m : ℕ) :
    IsConsistent (fun _ : LabeledSample Bool Bool m => zeroConcept)
      ({zeroConcept} : ConceptClass Bool Bool) := by
  intro S hS
  obtain ⟨c, hc, hlabels⟩ := hS
  have hc' : c = zeroConcept := mem_singleton_iff.mp hc
  subst c
  exact ⟨rfl, fun i => (hlabels i).symm⟩

theorem singleton_zero_samples :
    IsConsistent (fun _ : LabeledSample Bool Bool 0 => zeroConcept)
      ({zeroConcept} : ConceptClass Bool Bool) ∧
    (Measure.pi (fun _ : Fin 0 => uniform.map (fun x => (x, false))))
      {S : LabeledSample Bool Bool 0 | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false)))
          ((fun _ => zeroConcept) S)} = 0 := by
  exact ⟨singleton_consistent 0, by simp [target_risk_zero]⟩

theorem singleton_log_card :
    Real.log (({zeroConcept} : ConceptClass Bool Bool).ncard : ℝ) = 0 := by
  simp

theorem empirical_bridge (m : ℕ) (S : LabeledSample Bool Bool m)
    (hS : Realizable twoConcepts S) :
    empiricalError (learner m S) S = 0 :=
  (learner_consistent m).empiricalError_eq_zero S hS

theorem literal_family_interface :
    IsPACLearnerFor 16 quarter quarter twoConcepts
      {D | ∃ P : Measure Bool, IsProbabilityMeasure P ∧
        ∃ c ∈ twoConcepts, Measurable c ∧
          D = P.map (fun x => (x, c x))} := by
  exact (learner_consistent 16).isPACLearnerFor_of_finite
    twoConcepts_finite twoConcepts_nonempty twoConcepts_graphs
    quarter quarter sixteen_meets_log_bound _ (fun _ hD => hD)

theorem literal_family_populated :
    uniform.map (fun x => (x, false)) ∈
      {D | ∃ P : Measure Bool, IsProbabilityMeasure P ∧
        ∃ c ∈ twoConcepts, Measurable c ∧
          D = P.map (fun x => (x, c x))} := by
  exact ⟨uniform, inferInstance, zeroConcept,
    by simp [twoConcepts], measurable_const, rfl⟩

theorem too_few_samples :
    ¬ (Measure.pi (fun _ : Fin 1 => uniform.map (fun x => (x, false))))
      {S | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) (learner 1 S)} ≤
      (quarter.val : ℝ≥0∞) := by
  rw [one_sample_positive_failure]
  norm_num [quarter, ENNReal.inv_le_inv]

/-- The existential PAC predicate holds, but does not bless every learner. -/
theorem singleton_pac_zero_samples :
    IsPACLearnerFor 0 quarter quarter
      ({zeroConcept} : ConceptClass Bool Bool)
      {uniform.map (fun x => (x, false))} := by
  refine ⟨fun _ => zeroConcept, ?_⟩
  intro D _ hD
  have hD' := mem_singleton_iff.mp hD
  subst D
  simp [target_risk_zero]

theorem exchanged_witness_fails :
    (Measure.pi (fun _ : Fin 0 => uniform.map (fun x => (x, false))))
      {S : LabeledSample Bool Bool 0 | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false))) ((fun _ => id) S)} = 1 := by
  have hbad : (quarter.val : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) := by
    norm_num [quarter, ENNReal.inv_lt_inv]
  simp only [nonconstant_risk, hbad]
  exact measure_univ

/-- The memorizer fits the observed label but is improper for the singleton. -/
def memorizer : Learner Bool Bool 1 := fun S x =>
  if x = (S 0).1 then (S 0).2 else true

theorem improper_memorizer :
    (∀ _i : Fin 1, memorizer (fun _ => (false, false))
      ((false, false) : Bool × Bool).1 =
        ((false, false) : Bool × Bool).2) ∧
    ¬ IsConsistent memorizer ({zeroConcept} : ConceptClass Bool Bool) := by
  constructor
  · intro _
    simp [memorizer]
  intro h
  have hout := h.output_mem_conceptClass (fun _ => (false, false))
    ⟨zeroConcept, rfl, fun _ => rfl⟩
  have heq := mem_singleton_iff.mp hout
  have htrue := congrFun heq true
  simp [memorizer] at htrue

theorem realizable_benchmark_zero :
    optimalError (uniform.map (fun x => (x, false))) twoConcepts = 0 := by
  apply le_antisymm _ bot_le
  exact iInf_le_of_le zeroConcept
    (iInf_le_of_le (by simp [twoConcepts]) target_risk_zero.le)

theorem singleton_zero_sample_exponential_bound :
    (Measure.pi (fun _ : Fin 0 => uniform.map (fun x => (x, false))))
      {S : LabeledSample Bool Bool 0 | (quarter.val : ℝ≥0∞) <
        error (uniform.map (fun x => (x, false)))
          ((fun _ => zeroConcept) S)} ≤ 1 := by
  have h := (singleton_consistent 0).failure_le_exp
    (finite_singleton zeroConcept)
    (fun _ _ => Set.toFinite _ |>.measurableSet)
    quarter uniform (mem_singleton zeroConcept) measurable_const
  simpa using h

end Cslib.MachineLearning.PACLearning.FiniteClassTests
